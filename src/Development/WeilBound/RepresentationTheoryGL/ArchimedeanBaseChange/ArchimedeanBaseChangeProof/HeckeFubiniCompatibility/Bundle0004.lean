module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSmoothB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproA
section
noncomputable section

open MeasureTheory NumberField GlobalTheory.CuspRep

namespace PositivityTheory.Rg.BcB.CG.ReproA

section Fin

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem hasCompactSupport_prod {ι : Type} [Fintype ι] (a : ι → G → ℂ) (ha' : ∀ i, HasCompactSupport (a i))
    (f : (ι → G) → ℂ) : HasCompactSupport fun y : ι → G => (∏ i, a i (y i)) * f y := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun i => ha' i) fun y hy => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hy
  obtain ⟨i, hi⟩ := hy
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport (f := a i) hi), zero_mul]

theorem continuous_prod_mul {ι : Type} [Fintype ι] (a : ι → G → ℂ) (ha : ∀ i, Continuous (a i))
    (f : (ι → G) → ℂ) (hf : Continuous f) : Continuous fun y : ι → G => (∏ i, a i (y i)) * f y :=
  (continuous_finsetProd _ fun i _ => (ha i).comp (continuous_apply i)).mul hf

theorem cons_one_mul (n : ℕ) (z : Fin n → G) (j : Fin n) (t : G) :
    (Fin.cons 1 (z * Pi.mulSingle j t) : Fin (n + 1) → G) = Fin.cons 1 z * Pi.mulSingle j.succ t := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Fin.succ_ne_zero]
  · simp only [Fin.cons_succ, Pi.mul_apply, Pi.mulSingle_apply, Fin.succ_inj]

theorem cons_mul_single (n : ℕ) (z : Fin n → G) (t : G) :
    (Fin.cons 1 z : Fin (n + 1) → G) * Pi.mulSingle 0 t = Fin.cons t z := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · simp [Fin.succ_ne_zero]

variable (μ : Measure G) [μ.IsHaarMeasure]

theorem integral_fin_repro : ∀ (n : ℕ) (a : Fin n → G → ℂ), (∀ i, Continuous (a i)) → (∀ i, HasCompactSupport (a i)) →
    ∀ (f : (Fin n → G) → ℂ), Continuous f → ∀ (s : Fin n → ℂ),
    (∀ i y, ∫ t, a i t * f (y * Pi.mulSingle i t) ∂μ = s i * f y) →
    ∫ y, (∏ i, a i (y i)) * f y ∂(Measure.pi fun _ => μ) = (∏ i, s i) * f 1
  | 0, a, _, _, f, _, s, _ => by
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ) 1, integral_dirac]
    simp
  | n + 1, a, ha, ha', f, hf, s, h => by
    set e : (Fin (n + 1) → G) ≃ᵐ G × (Fin n → G) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
      measurePreserving_piFinSuccAbove (α := fun _ : Fin (n + 1) => G) (fun _ => μ) 0
    set F : (Fin (n + 1) → G) → ℂ := fun y => (∏ i, a i (y i)) * f y with hF
    have hFi : Integrable F (Measure.pi fun _ => μ) :=
      (continuous_prod_mul a ha f hf).integrable_of_hasCompactSupport (hasCompactSupport_prod a ha' f)
    have e1 : ∫ y, F y ∂(Measure.pi fun _ => μ) = ∫ p, F (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
      rw [← hmp.integral_comp' (fun p => F (e.symm p))]
      simp
    have hsymm : ∀ p : G × (Fin n → G), e.symm p = Fin.cons p.1 p.2 := by
      intro p
      rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact Fin.insertNth_zero' _ _
    have hGi : Integrable (fun p => F (e.symm p)) (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
      have := (hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding (g := F)
      exact this.2 hFi
    change ∫ y, F y ∂(Measure.pi fun _ => μ) = _
    rw [e1, integral_prod_symm _ hGi]
    have e2 : ∀ z : Fin n → G, ∫ t, F (e.symm (t, z)) ∂μ =
        (∏ j, a j.succ (z j)) * (s 0 * f (Fin.cons 1 z)) := by
      intro z
      rw [← h 0 (Fin.cons 1 z), ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [hsymm, hF, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, cons_mul_single]
      ring
    simp_rw [e2]
    set a' : Fin n → G → ℂ := fun j => a j.succ
    set f' : (Fin n → G) → ℂ := fun z => f (Fin.cons 1 z)
    have hf' : Continuous f' := hf.comp (continuous_const.finCons continuous_id)
    have h' : ∀ j z, ∫ t, a' j t * f' (z * Pi.mulSingle j t) ∂μ = s j.succ * f' z := by
      intro j z
      simp only [a', f', cons_one_mul]
      exact h j.succ (Fin.cons 1 z)
    have ih := integral_fin_repro n a' (fun j => ha j.succ) (fun j => ha' j.succ) f' hf' (fun j => s j.succ) h'
    have e3 : ∀ z : Fin n → G, (∏ j, a j.succ (z j)) * (s 0 * f (Fin.cons 1 z)) =
        s 0 * ((∏ j, a' j (z j)) * f' z) := fun z => by simp only [a', f']; ring
    simp_rw [e3]
    rw [integral_const_mul, ih, Fin.prod_univ_succ]
    have e4 : f' 1 = f 1 := by
      simp only [f']
      congr 1
      funext k
      refine Fin.cases ?_ (fun k => ?_) k <;> simp
    rw [e4]
    ring

end Fin

theorem integral_pi_repro {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (a : ι → G → ℂ) (ha : ∀ i, Continuous (a i))
    (ha' : ∀ i, HasCompactSupport (a i)) (f : (ι → G) → ℂ) (hf : Continuous f) (s : ι → ℂ)
    (h : ∀ i y, ∫ t, a i t * f (y * Pi.mulSingle i t) ∂μ = s i * f y) :
    ∫ y, (∏ i, a i (y i)) * f y ∂(Measure.pi fun _ => μ) = (∏ i, s i) * f 1 := by
  set e := Fintype.equivFin ι
  set Φ := MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl G) with hΦ
  have hmp : MeasurePreserving Φ (Measure.pi fun _ : Fin (Fintype.card ι) => μ) (Measure.pi fun _ : ι => μ) :=
    measurePreserving_arrowCongr' _ _ e.symm (MeasurableEquiv.refl G) fun _ => MeasurePreserving.id μ
  have hΦa : ∀ z : Fin (Fintype.card ι) → G, Φ z = fun i => z (e i) := by
    intro z; funext i; rfl
  rw [← hmp.integral_comp' (fun y => (∏ i, a i (y i)) * f y)]
  simp_rw [hΦa]
  set a' : Fin (Fintype.card ι) → G → ℂ := fun k => a (e.symm k)
  set f' : (Fin (Fintype.card ι) → G) → ℂ := fun z => f fun i => z (e i)
  have e1 : ∀ z : Fin (Fintype.card ι) → G, (∏ i, a i (z (e i))) * f (fun i => z (e i)) =
      (∏ k, a' k (z k)) * f' z := by
    intro z
    simp only [a', f']
    congr 1
    exact Fintype.prod_equiv e _ _ fun i => by simp
  simp_rw [e1]
  have hf' : Continuous f' := hf.comp (continuous_pi fun i => continuous_apply (e i))
  have hmul : ∀ (z : Fin (Fintype.card ι) → G) (k : Fin (Fintype.card ι)) (t : G),
      (fun i => (z * Pi.mulSingle k t : Fin (Fintype.card ι) → G) (e i)) =
        (fun i => z (e i)) * Pi.mulSingle (e.symm k) t := by
    intro z k t
    funext i
    simp only [Pi.mul_apply, Pi.mulSingle_apply]
    by_cases hi : i = e.symm k
    · subst hi; simp
    · have : e i ≠ k := fun h' => hi (by rw [← h']; simp)
      simp [hi, this]
  have h' : ∀ k z, ∫ t, a' k t * f' (z * Pi.mulSingle k t) ∂μ = s (e.symm k) * f' z := by
    intro k z
    simp only [a', f', hmul]
    exact h (e.symm k) _
  rw [integral_fin_repro μ _ a' (fun k => ha _) (fun k => ha' _) f' hf' _ h']
  have e2 : f' 1 = f 1 := rfl
  rw [e2]
  congr 1
  exact Fintype.prod_equiv e.symm _ _ fun k => rfl

theorem pi_isHaar {ι : Type} [Fintype ι] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : (Measure.pi fun _ : ι => μ).IsHaarMeasure := by
  infer_instance

theorem haar_restrict_eq {X A : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
    [BorelSpace X] [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (ν : Measure X) [ν.IsHaarMeasure] (lam0 : Measure A) [lam0.IsHaarMeasure] (P : X →* A) (hP : Continuous P)
    (σ : A →* X) (hσ : ∀ a, P (σ a) = a) (U0 : Subgroup X) (hU0 : IsOpen (U0 : Set X)) (hσU : ∀ a, σ a ∈ U0)
    (hprop : ∀ C : Set A, IsCompact C → ∃ D : Set X, IsCompact D ∧ (U0 : Set X) ∩ P ⁻¹' C ⊆ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : A → ℂ, Continuous F → HasCompactSupport F →
      ∫ x, (U0 : Set X).indicator (fun x => F (P x)) x ∂ν = c * ∫ a, F a ∂lam0 := by
  have hPm : Measurable P := hP.measurable
  have hU0m : MeasurableSet (U0 : Set X) := hU0.measurableSet
  set lam : Measure A := Measure.map P (ν.restrict U0) with hlam
  have hinv : lam.IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    have hf : Measurable fun x : X => σ a * x := measurable_const_mul (σ a)
    have hpre : (fun x : X => σ a * x) ⁻¹' (U0 : Set X) = U0 := by
      ext x
      simp only [Set.mem_preimage, SetLike.mem_coe]
      exact ⟨fun h => by simpa using U0.mul_mem (U0.inv_mem (hσU a)) h, fun h => U0.mul_mem (hσU a) h⟩
    have e1 : Measure.map (fun x : X => σ a * x) (ν.restrict U0) = ν.restrict U0 := by
      conv_lhs => rw [← hpre]
      rw [← Measure.restrict_map hf hU0m, map_mul_left_eq_self]
    rw [hlam, Measure.map_map (measurable_const_mul a) hPm]
    have e2 : (fun x : A => a * x) ∘ P = P ∘ fun x : X => σ a * x := by
      funext x; simp [hσ]
    rw [e2, ← Measure.map_map hPm hf, e1]
  have hfin : IsFiniteMeasureOnCompacts lam := by
    refine ⟨fun C hC => ?_⟩
    obtain ⟨D, hD, hsub⟩ := hprop C hC
    rw [hlam, Measure.map_apply hPm hC.isClosed.measurableSet, Measure.restrict_apply (hPm hC.isClosed.measurableSet)]
    refine lt_of_le_of_lt (measure_mono ?_) hD.measure_lt_top
    intro x hx
    exact hsub ⟨hx.2, hx.1⟩
  have heq := Measure.isMulLeftInvariant_eq_smul lam lam0
  set c' := Measure.haarScalarFactor lam lam0 with hc'
  have hpos : c' ≠ 0 := by
    intro h0
    have h1 : lam Set.univ = 0 := by rw [heq, h0]; simp
    rw [hlam, Measure.map_apply hPm MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter] at h1
    exact (hU0.measure_ne_zero ν ⟨1, U0.one_mem⟩) h1
  refine ⟨(c' : ℝ), lt_of_le_of_ne c'.2 (fun h => hpos (NNReal.coe_eq_zero.1 h.symm)), fun F hF _ => ?_⟩
  rw [integral_indicator hU0m, ← integral_map hPm.aemeasurable hF.aestronglyMeasurable, ← hlam]
  conv_lhs => rw [heq]
  rw [integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

theorem exists_compact_open_le (E : Type) [Field E] [NumberField E] (N : ℕ) (K : Subgroup (GL (Fin N) (Af E)))
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) :
    ∃ K0 : Subgroup (GL (Fin N) (Af E)), K0 ≤ K ∧ IsOpen (K0 : Set (GL (Fin N) (Af E))) ∧
      IsCompact (K0 : Set (GL (Fin N) (Af E))) := by
  obtain ⟨U, hUo, hUc⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E N
  refine ⟨K ⊓ U, inf_le_left, ?_, ?_⟩
  · exact hK.inter hUo
  · exact hUc.inter_left (K.isClosed_of_isOpen hK)

end PositivityTheory.Rg.BcB.CG.ReproA
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSmooth
section
noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped ContDiff Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

namespace SmoothIntegrals

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def entL (M : KMod n) (i j : Ix M) : (M.V →L[ℂ] M.V) →L[ℝ] ℂ :=
  ((innerSL ℂ (stdOrthonormalBasis ℂ M.V i)).comp
    (ContinuousLinearMap.apply ℂ M.V (stdOrthonormalBasis ℂ M.V j))).restrictScalars ℝ

theorem mult_contDiffOn [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ M k val T) : ContDiffOn ℝ ∞ k (GLs n) := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  exact (ContDiffOn.sum fun i _ => ((hks i).2.1).const_smul (c i)).congr fun y hy => hk y hy

theorem ent_contDiffOn [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ M k val T) (i j : Ix M) :
    ContDiffOn ℝ ∞ (fun A => ent M (k A) i j) (GLs n) :=
  (entL M i j).contDiff.comp_contDiffOn (mult_contDiffOn h)

theorem continuous_entA [MeasurableSpace (G n)] {μ : Measure (G n)} {M : Mods E n} {k : Kers M}
    {val : InfinitePlace E → Inf n → ℂ} {T : ℝ} (h : IsMults μ k val T) (I J : IxA M) :
    Continuous fun g : GA E n => entA k I J g :=
  continuous_finsetProd _ fun v _ => (entL (M v) (I v) (J v)).continuous.comp
    ((mult_contDiffOn (h v)).continuousOn.comp_continuous (Units.continuous_val.comp (continuous_gI v))
      fun _ => val_mem_GLs₀ _)

omit [IsCMField E] in
theorem continuous_gFin₀ : Continuous (gFin : GA E n → GL (Fin n) (Af E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_snd)

theorem continuous_hFin₀ {a b : ℕ} : Continuous (hFin : H E a b → Hf E a b) :=
  (continuous_gFin₀.comp continuous_fst).prodMk (continuous_gFin₀.comp continuous_snd)

theorem gFin_infGL₀ (u : GL (Fin n) (Cinf E)) : gFin (infGL E n u) = 1 := pFin_infGL u

end SmoothIntegrals


open SmoothIntegrals in
theorem smoothOf (hTT : TensTest) : SmoothOf := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro E _ _ _ a b _ _ _ _ μa _ μb _ Ma Mb ι _ D ka kb va vb T ψ U f hka hkb hψ _ _ hR
    have : BorelSpace (H E a b) := ⟨rfl⟩
    have : D.μ.IsMulLeftInvariant := D.haar.1
    have : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
    have : IsFiniteMeasureOnCompacts D.μ := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    obtain ⟨hfc, c, hc, hconv⟩ := hR
    have hTest := (hTT E a b μa μb Ma Mb ι ka kb va vb T ψ hka hkb hψ).1
    have hψc : ∀ x y, Continuous fun w : H E a b => ψ x y (hFin w) := fun x y => (hψ x y).1.comp continuous_hFin₀

    have hrep : ∀ i z, f i z = c⁻¹ * ∑ j, ∫ y, tens ka kb ψ i j y * f j (z * y) ∂D.μ := by
      intro i z
      have h1 := congrFun (congrFun hconv i) z
      have h2 : c * f i z = ∑ j, ∫ y, tens ka kb ψ i j y * f j (z * y) ∂D.μ := h1.symm
      rw [← h2, inv_mul_cancel_left₀ hc]
    refine ⟨fun i m₂ => ?_, fun i m₁ => ?_⟩
    · have hj : ∀ j, (fun x => ∫ y, tens ka kb ψ i j y * f j ((x, m₂) * y) ∂D.μ) ∈ Sm E a := by
        intro j
        have h := mem_Sm_conv D.μ (MonoidHom.inl (GA E a) (GA E b)) (continuous_id.prodMk continuous_const) Prod.fst
          continuous_fst (fun h w => by simp) (fun v A => ent (Ma v) (ka v A) (i.1.1 v) (j.1.1 v))
          (fun v => ent_contDiffOn (hka v) _ _) (fun w => entA kb i.1.2 j.1.2 w.2 * ψ i.2 j.2 (hFin w))
          (((continuous_entA hkb _ _).comp continuous_snd).mul (hψc _ _))
          (fun _ w => by simp [hFin, gFin_infGL₀]) (f j) (hfc j) (tens ka kb ψ i j) (fun w => mul_assoc _ _ _)
          (hTest i j).2 ((1 : GA E a), m₂)
        have e : ∀ x : GA E a, ((1 : GA E a), m₂) * MonoidHom.inl (GA E a) (GA E b) x = (x, m₂) := fun x =>
          Prod.ext (one_mul x) (mul_one m₂)
        simpa only [e] using h
      refine ⟨⟨c⁻¹ • ∑ j, fun x => ∫ y, tens ka kb ψ i j y * f j ((x, m₂) * y) ∂D.μ,
        (Sm E a).smul_mem c⁻¹ ((Sm E a).sum_mem fun j _ => hj j)⟩, ?_⟩
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact (hrep i (x, m₂)).symm
    · have hj : ∀ j, (fun x => ∫ y, tens ka kb ψ i j y * f j ((m₁, x) * y) ∂D.μ) ∈ Sm E b := by
        intro j
        have h := mem_Sm_conv D.μ (MonoidHom.inr (GA E a) (GA E b)) (continuous_const.prodMk continuous_id) Prod.snd
          continuous_snd (fun h w => by simp) (fun v A => ent (Mb v) (kb v A) (i.1.2 v) (j.1.2 v))
          (fun v => ent_contDiffOn (hkb v) _ _) (fun w => entA ka i.1.1 j.1.1 w.1 * ψ i.2 j.2 (hFin w))
          (((continuous_entA hka _ _).comp continuous_fst).mul (hψc _ _))
          (fun _ w => by simp [hFin, gFin_infGL₀]) (f j) (hfc j) (tens ka kb ψ i j)
          (fun w => by
            show entA ka _ _ w.1 * entA kb _ _ w.2 * ψ _ _ (hFin w) = entA kb _ _ w.2 * (entA ka _ _ w.1 * ψ _ _ (hFin w))
            ring)
          (hTest i j).2 (m₁, (1 : GA E b))
        have e : ∀ x : GA E b, (m₁, (1 : GA E b)) * MonoidHom.inr (GA E a) (GA E b) x = (m₁, x) := fun x =>
          Prod.ext (mul_one m₁) (one_mul x)
        simpa only [e] using h
      refine ⟨⟨c⁻¹ • ∑ j, fun x => ∫ y, tens ka kb ψ i j y * f j ((m₁, x) * y) ∂D.μ,
        (Sm E b).smul_mem c⁻¹ ((Sm E b).sum_mem fun j _ => hj j)⟩, ?_⟩
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact (hrep i (m₁, x)).symm

end PositivityTheory.Rg.BcB.CG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PackOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH TypeH HeckeM heckeAct Repro)
open PositivityTheory.RgBcC.Bridge (along)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

def ValCont : Prop := ∀ (n : ℕ) [MeasurableSpace (G n)] (μ : Measure (G n)) (M : KMod n) (k : Mat n → (M.V →L[ℂ] M.V))
  (val : Inf n → ℂ) (T : ℝ) (χ : ℕ → Inf n) (χ₀ : Inf n), IsMult μ M k val T →
  (∀ s m, Tendsto (fun j => GlobalTheory.Dec.gelfVal (χ j s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χ₀ s) m))) →
  Tendsto (fun j => val (χ j)) atTop (𝓝 (val χ₀))

def Pack : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a) (Mb : Mods E b),
  ∃ (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W₁ ∧ FiniteDimensional ℂ W₂ ∧
  ∀ (D : Dom E a b) [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
    [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
    (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure] (κ : Type) [Fintype κ]
    (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)) (g : ℝ → ℝ)
    (ka' : Bool → ℕ → Kers Ma) (kb' : Bool → ℕ → Kers Mb) (K₁ : Subgroup (GL (Fin a) (Af E)))
    (K₂ : Subgroup (GL (Fin b) (Af E))) (M : ℕ) (f : Io Ma Mb κ → H E a b → ℂ) (c : ℂ)
    (ca cb : InfinitePlace E → Bool → ℕ → ℂ), Compat D μa μb ν → IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ →
    IsBump g T → (∀ v, IsKer μa (Ma v) [] g (ka v)) → (∀ v, IsKer μb (Mb v) [] g (kb v)) →
    (∀ s m v, IsKer μa (Ma v) [(s, m)] g (ka' s m v)) → (∀ s m v, IsKer μb (Mb v) [(s, m)] g (kb' s m v)) →
    IsOpen (K₁ : Set (GL (Fin a) (Af E))) → IsOpen (K₂ : Set (GL (Fin b) (Af E))) →
    (∀ x y, ∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, ∀ h, ψ x y ((u₁, u₂) * h) = ψ x y h) →
    (∀ i, Continuous (f i)) → f ≠ 0 → LeftInv f → WL2 D M f → c ≠ 0 →
    PositivityTheory.Rg.BcB.E.conv D.μ (tens ka kb ψ) f = c • f →
    (∀ v s m, PositivityTheory.Rg.BcB.E.conv D.μ (tens (Function.update ka v (ka' s m v)) kb ψ) f = ca v s m • f) →
    (∀ v s m, PositivityTheory.Rg.BcB.E.conv D.μ (tens ka (Function.update kb v (kb' s m v)) ψ) f = cb v s m • f) →
    ∃ (χa : InfinitePlace E → Inf a) (χb : InfinitePlace E → Inf b),
      (∀ v s m, GlobalTheory.Dec.gelfVal (χa v s) m = ca v s m / c) ∧ (∀ v s m, GlobalTheory.Dec.gelfVal (χb v s) m = cb v s m / c) ∧
      EigAll χa χb f ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) ∧
      (∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ (∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) ∧
      (∀ φ ∈ slices₁ f, IsAutForm φ) ∧ (∀ φ ∈ slices₂ f, IsAutForm φ) ∧
      (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₁ f)) τ (mOf χa τ)) ∧
      ∀ τ, HasInfCharGL (Submodule.span ℂ (slices₂ f)) τ (mOf χb τ)

theorem pack_of (h1 : TensTest) (h2 : TypeOf) (h3 : SmoothOf) (h4 : GrowthOf) (h5 : GelOf) (h6 : InfEx) (h7 : AutOf) :
    Pack := by
  intro E _ _ _ a b Ma Mb
  obtain ⟨W₁, W₂, f₁, f₂, hW⟩ := h2 E a b Ma Mb
  refine ⟨W₁, W₂, f₁, f₂, ?_⟩
  intro D _ _ _ _ _ _ μa _ μb _ ν _ κ _ ka kb va vb T ψ g ka' kb' K₁ K₂ M f c ca cb hC hka hkb hψ hg k0a k0b k1a k1b
    o₁ o₂ hlev hf hf0 hL hW2 hc he hea heb
  have hR : Repr D ka kb ψ f := ⟨hf, c, hc, he⟩
  have hty := hW D μa μb κ ka kb va vb T ψ K₁ K₂ f hka hkb hψ hlev hR
  obtain ⟨s₁, s₂⟩ := h3 E a b μa μb Ma Mb κ D ka kb va vb T ψ (K₁.prod K₂) f hka hkb hψ (o₁.prod o₂)
    (fun x y u hu h => hlev x y u.1 hu.1 u.2 hu.2 h) hR
  obtain ⟨C, N, hG⟩ := h4 E a b D _ _ M f c (h1 E a b μa μb Ma Mb κ ka kb va vb T ψ hka hkb hψ).1 hf hL hW2 hc he
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hf0
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hi₀
  have ga := fun v s m => (h5 E a b D μa μb ν Ma Mb κ ka kb va vb T ψ f c (ca v s m) v g s m hC hka hkb hψ hg ⟨s₁, s₂⟩ hf hc he).1
    _ (k0a v) (k1a s m v) (hea v s m)
  have gb := fun v s m => (h5 E a b D μa μb ν Ma Mb κ ka kb va vb T ψ f c (cb v s m) v g s m hC hka hkb hψ hg ⟨s₁, s₂⟩ hf hc he).2
    _ (k0b v) (k1b s m v) (heb v s m)
  have ea : ∀ v, ∃ χ : Inf a, ∀ s m, GlobalTheory.Dec.gelfVal (χ s) m = ca v s m / c := fun v => by
    obtain ⟨φ, hφ⟩ := s₁ i₀ x₀.2
    refine h6 E a {φ} v (fun s m => ca v s m / c) ⟨φ, rfl, fun e => hx₀ ?_⟩ ?_
    · have := congrFun hφ x₀.1
      rw [e] at this
      exact this.symm
    · rintro _ rfl y s m x hx
      rw [hφ]
      exact ga v s m i₀ y x₀.2 x hx
  have eb : ∀ v, ∃ χ : Inf b, ∀ s m, GlobalTheory.Dec.gelfVal (χ s) m = cb v s m / c := fun v => by
    obtain ⟨φ, hφ⟩ := s₂ i₀ x₀.1
    refine h6 E b {φ} v (fun s m => cb v s m / c) ⟨φ, rfl, fun e => hx₀ ?_⟩ ?_
    · have := congrFun hφ x₀.2
      rw [e] at this
      exact this.symm
    · rintro _ rfl y s m x hx
      rw [hφ]
      exact gb v s m i₀ y x₀.1 x hx
  choose χa hχa using ea
  choose χb hχb using eb
  have hE : EigAll χa χb f :=
    ⟨fun i v y m₂ s m x hx => by rw [hχa]; exact ga v s m i y m₂ x hx,
      fun i v y m₁ s m x hx => by rw [hχb]; exact gb v s m i y m₁ x hx⟩
  obtain ⟨a₁, a₂, a₃, a₄⟩ := h7 E a b _ f K₁ K₂ W₁ W₂ χa χb C N o₁ o₂ f₁ f₂ hL hty hG hE
  exact ⟨χa, χb, hχa, hχb, hE, hty, s₁, s₂, a₁, a₂, a₃, a₄⟩

end PositivityTheory.Rg.BcB.CG

end
end

