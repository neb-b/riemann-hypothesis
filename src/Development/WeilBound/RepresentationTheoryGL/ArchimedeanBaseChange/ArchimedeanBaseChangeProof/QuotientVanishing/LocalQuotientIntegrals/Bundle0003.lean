module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0050

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PClassVanish
section
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.CV.ClassVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

theorem exists_haar_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] (hc : ∀ a b : G, a * b = b * a) :
    ∃ ν : Measure G, ν.IsHaarMeasure ∧ ν.IsInvInvariant := by
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hc }
  exact ⟨Measure.haar, inferInstance, Measure.IsHaarMeasure.isInvInvariant_of_regular _⟩

theorem gamma_fin_zero (y : (Fin 0 → SignType) → ℝ) (a : Fin 0 → ℝ) : gam y a = 1 := by
  unfold gam gamOn
  rw [Finset.sum_eq_single (∅ : Finset (Fin 0 → SignType))]
  · simp
  · intro s hs hne
    exfalso
    apply hne
    simp only [Finset.mem_filter] at hs
    exact Finset.subset_empty.mp fun e he => absurd (Subsingleton.elim e 0 ▸ he) hs.2.1
  · intro h
    exfalso
    apply h
    simp [Finset.mem_filter]

theorem quot_congr {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) {H H' : Subgroup G} (h : H = H')
    (F : G → ℂ) : quotIntegral μ H Measure.count F = quotIntegral μ H' Measure.count F := by
  subst h; rfl

theorem quotL_congr {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) {H H' : Subgroup G} (h : H = H')
    (F : G → ENNReal) : quotLIntegral μ H Measure.count F = quotLIntegral μ H' Measure.count F := by
  subst h; rfl

end PositivityTheory.Rg.BcB.CV.ClassVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem PositivityTheory.Rg.BcB.CV.pf_ClassVanish : PositivityTheory.Rg.BcB.D4.PairParam → PositivityTheory.Rg.BcB.D4.TorusChar → PositivityTheory.Rg.BcB.D4.ChiGam → PositivityTheory.Rg.BcB.D4.QuotStage → PositivityTheory.Rg.BcB.D4.RatDisc → PositivityTheory.Rg.BcB.SizeBasic → PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.Vfun → PositivityTheory.Rg.BcB.CV.AdTop → PositivityTheory.Rg.BcB.CV.CutInt → PositivityTheory.Rg.BcB.CV.Glob1 → PositivityTheory.Rg.BcB.CV.Glob2 → PositivityTheory.Rg.BcB.ClassVanish := by
  intro hPP hTC hCG hQS hRD hSB hQA hVf hAT hCI hG1 hG2
  intro E _ _ _ _ n
  obtain ⟨C₀, hC₀⟩ := hCG E n
  refine ⟨max 0 C₀, ?_⟩
  intro _ _ μ _ τ r φ d hφ hsz hvc hτ hreg hne
  obtain ⟨hLC, hT2, hSC, -, -, -⟩ := hAT E n
  haveI := hLC
  haveI := hT2
  haveI := hSC
  obtain ⟨m, Wof, hiso, huniq, hzero, hmeet, hmono, hperp⟩ := hPP E n d hreg
  obtain ⟨hcomm, a, hdegT, hadd, hrat0, hcont, hcpt⟩ := hTC E n d m Wof hiso huniq hzero hmeet hmono hreg
  obtain ⟨hle, hdisc, hclosed⟩ := hRD.1 E n d
  haveI : LocallyCompactSpace (adCent d) := hclosed.locallyCompactSpace
  haveI : BorelSpace (adCent d) := Subtype.borelSpace _
  haveI : SecondCountableTopology (adCent d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hcommT : ∀ s t : adCent d, s * t = t * s := fun s t => Subtype.ext (hcomm s s.2 t t.2)
  obtain ⟨ν, hνH, hνI⟩ := ClassVanishing.exists_haar_inv hcommT
  haveI := hνH
  haveI := hνI
  have hmap : (ratIn d).map (adCent d).subtype = ratCent d := by
    rw [ratIn, Subgroup.subgroupOf_map_subtype, inf_of_le_left hle]
  set F : GA E n → ℂ := fun x => chiT τ x * φ (twConj (thetaA E n) x (ratGL E n d)) with hF
  obtain ⟨hFm, hFinv, hFfin⟩ := hCI E n μ τ φ d hφ
  have hstage := hQS (GA E n) μ (adCent d) ν (ratIn d) F hclosed hdisc hFm
    (fun g hg x => hFinv g (Subgroup.mem_subgroupOf.1 hg) x)
    (by rw [ClassVanishing.quotL_congr μ hmap]; exact hFfin)
  rw [ClassVanishing.quot_congr μ hmap] at hstage

  obtain ⟨V, hVdef⟩ : ∃ V : ((Fin m → SignType) → ℝ) → ℂ,
      V = fun y => quotIntegral ν (ratIn d) Measure.count fun t : adCent d => (gam y (a t) : ℂ) := ⟨_, rfl⟩
  have hcptT : ∀ M : ℝ, ∃ K : Set (adCent d), IsCompact K ∧ ∀ t : adCent d, (∀ i, |a t i| ≤ M) →
      t ∈ ((ratIn d : Subgroup (adCent d)) : Set (adCent d)) * K := by
    intro M
    obtain ⟨K, hK, hKt⟩ := hcpt M
    refine ⟨Subtype.val ⁻¹' K, hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hK, fun t ht => ?_⟩
    obtain ⟨g, hg, k, hk, hgk⟩ := Set.mem_mul.1 (hKt t t.2 ht)
    have hgA : g ∈ adCent d := hle hg
    have hkA : k ∈ adCent d := by
      have : k = g⁻¹ * t := by rw [← hgk]; group
      rw [this]; exact (adCent d).mul_mem ((adCent d).inv_mem hgA) t.2
    exact Set.mem_mul.2 ⟨⟨g, hgA⟩, hg, ⟨k, hkA⟩, hk, Subtype.ext hgk⟩
  obtain ⟨hVP, hVtr⟩ := hVf (adCent d) ν (ratIn d) m (fun t => a t) hcommT hdisc
    (continuousOn_iff_continuous_domRestrict.1 hcont) (fun s t => hadd s s.2 t t.2)
    (fun t ht => hrat0 t (Subgroup.mem_subgroupOf.1 ht)) hcptT
  rw [← hVdef] at hVP
  have hVinv : ∀ t ∈ adCent d, ∀ y, V (fun e => y e - sdot e (a t)) = V y := by
    intro t ht y
    have := hVtr y ⟨t, ht⟩
    rw [hVdef]
    exact this

  have hinner : ∀ x, (quotIntegral ν (ratIn d) Measure.count fun t : adCent d => F ((t : GA E n) * x)) =
      φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x) := by
    intro x
    have hpt : (fun t : adCent d => F ((t : GA E n) * x)) =
        fun t : adCent d => φ (twConj (thetaA E n) x (ratGL E n d)) * (gam (yOf τ Wof x) (a t) : ℂ) := by
      funext t
      show chiT τ ((t : GA E n) * x) * φ (twConj (thetaA E n) ((t : GA E n) * x) (ratGL E n d)) = _
      rw [twConj_mul_left (thetaA E n) (ratGL E n d) t.2 x]
      by_cases h0 : φ (twConj (thetaA E n) x (ratGL E n d)) = 0
      · simp [h0]
      · have h1 := hsz _ h0
        have h2 := (hSB E n).2.1 (twConj (thetaA E n) x (ratGL E n d))
        have hτ' : C₀ * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) ≤ τ :=
          calc C₀ * (1 + logSize (twConj (thetaA E n) x (ratGL E n d)))
              ≤ max 0 C₀ * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
            _ ≤ max 0 C₀ * (1 + r) := mul_le_mul_of_nonneg_left (by linarith) (le_max_left _ _)
            _ ≤ τ := hτ
        exact (mul_comm _ _).trans
          (congrArg (fun z => φ (twConj (thetaA E n) x (ratGL E n d)) * z)
            (hC₀ d m Wof a hiso huniq hzero hmeet hmono hreg hdegT τ x hτ' t t.2))
    rw [hpt, (hQA (adCent d) ν (ratIn d) Measure.count).2.2 (φ (twConj (thetaA E n) x (ratGL E n d)))
      (fun t : adCent d => (gam (yOf τ Wof x) (a t) : ℂ)), hVdef]
  have hcut : cutTerm μ τ φ d = quotIntegral μ (adCent d) ν
      (fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x)) := by
    show quotIntegral μ (ratCent d) Measure.count F = _
    rw [hstage]
    congr 1
    funext x
    exact hinner x
  rw [hcut]
  by_cases hm : m = 0
  · subst hm
    have hV : ∀ y, V y = V 0 := fun y => by
      rw [hVdef]
      simp only [ClassVanishing.gamma_fin_zero]
    rw [show (fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x)) =
        fun x => V 0 * φ (twConj (thetaA E n) x (ratGL E n d)) from funext fun x => by rw [hV, mul_comm],
      (hQA (GA E n) μ (adCent d) ν).2.2 (V 0) (fun x => φ (twConj (thetaA E n) x (ratGL E n d))),
      hG1 E n μ d ν φ hreg hne hcomm hclosed hφ hvc, mul_zero]
  · exact hG2 E n m μ d ν Wof a V τ φ hm
      ⟨hreg, hiso, huniq, hzero, hmeet, hmono, hperp, hcomm, hclosed, hdegT⟩ hVP hVinv hφ hvc
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.POneVanish
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.FirstVanishingAlt

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem twConj_mul_left {n : ℕ} (d t x : GL (Fin n) ℂ) (ht : t ∈ twCent (thC n) d) :
    twConj (thC n) (t * x) d = twConj (thC n) x d := by
  rw [mem_twCent] at ht
  simp only [twConj, map_mul]
  calc (t * x)⁻¹ * d * ((thC n) t * (thC n) x) = x⁻¹ * (t⁻¹ * d * (thC n) t) * (thC n) x := by group
    _ = x⁻¹ * d * (thC n) x := by rw [ht]

theorem sle_refl {m : ℕ} (e : Fin m → SignType) : SLe e e := fun _ _ => rfl

def zr {m : ℕ} (z : (Fin m → SignType) → ℝ) (s : Finset (Fin m → SignType)) : (Fin m → SignType) → ℝ :=
  fun e => if e ∈ s then z e else 0

theorem zr_insert {m : ℕ} (z y : (Fin m → SignType) → ℝ) {s : Finset (Fin m → SignType)} {e : Fin m → SignType}
    (he : e ∉ s) : y + zr z (insert e s) = Function.update (y + zr z s) e (y e + z e) := by
  funext e'
  by_cases h : e' = e
  · subst h; simp [zr]
  · simp [zr, h]

theorem zr_self {m : ℕ} (z y : (Fin m → SignType) → ℝ) {s : Finset (Fin m → SignType)} {e : Fin m → SignType}
    (he : e ∉ s) : y + zr z s = Function.update (y + zr z s) e (y e) := by
  funext e'
  by_cases h : e' = e
  · subst h; simp [zr, he]
  · simp [h]

theorem diff_step {m : ℕ} {V : ((Fin m → SignType) → ℝ) → ℂ} (hV : VP V) (z : (Fin m → SignType) → ℝ)
    (s : Finset (Fin m → SignType)) (e : Fin m → SignType) (he : e ∉ s) (y y' : (Fin m → SignType) → ℝ)
    (hyy : ∀ e', SLe e e' ∨ SLe e' e → y e' = y' e') :
    V (y + zr z (insert e s)) - V (y + zr z s) = V (y' + zr z (insert e s)) - V (y' + zr z s) := by
  have key : ∀ w : (Fin m → SignType) → ℝ, V (w + zr z (insert e s)) - V (w + zr z s) =
      V (Function.update (w + zr z s) e (w e + z e)) - V (Function.update (w + zr z s) e (w e)) := fun w => by
    rw [← zr_insert z w he, ← zr_self z w he]
  have hee : y e = y' e := hyy e (Or.inl (sle_refl e))
  rw [key y, key y', hee]
  exact hV.diff _ _ e _ _ (fun e' h => by simp only [Pi.add_apply, hyy e' h])

theorem good_V {n m : ℕ} [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] {d : GL (Fin n) ℂ}
    {V : ((Fin m → SignType) → ℝ) → ℂ} {p : GL (Fin n) ℂ → (Fin m → SignType) → ℝ} (hV : VP V) (hL : LocFam d V p)
    (c : (Fin m → SignType) → ℝ) :
    Measurable (fun x => V (p x + c)) ∧ (∀ t ∈ twCent (thC n) d, ∀ x, V (p (t * x) + c) = V (p x + c)) ∧
      ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖V (p x + c)‖ ≤ B := by
  refine ⟨hV.meas.comp (hL.cont.add continuous_const).measurable, fun t ht x => hL.tor t ht x c, fun C hC => ?_⟩
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (f := fun x => p x + c) (hL.cont.add continuous_const).continuousOn
  obtain ⟨B, hB⟩ := hV.bdd M
  refine ⟨B, fun x hx => hB _ fun e => ?_⟩
  have := (norm_le_pi_norm (p x + c) e).trans (hM x hx)
  rwa [Real.norm_eq_abs] at this

end PositivityTheory.Rg.BcB.CV.FirstVanishingAlt

open PositivityTheory.Rg.BcB.CV.FirstVanishingAlt in
theorem PositivityTheory.Rg.BcB.CV.pf_OneVanish : PositivityTheory.Rg.BcB.LocVanish → PositivityTheory.Rg.BcB.D4.LocProper → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QInt → PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.OneVanish := by
  intro hLV hLP hLT hQI hQA n m _ _ μ _ d ν _ _ f V p z hsep hf hfs hfc hV hL hz0
  obtain ⟨hTc, -, hθc, hlc, hsc⟩ := hLT n d hsep
  have := hlc
  have := hsc
  have htc : Continuous (fun x : GL (Fin n) ℂ => twConj (thC n) x d) := by
    unfold twConj
    exact (continuous_inv.mul continuous_const).mul hθc
  obtain ⟨Bf, hBf⟩ := hf.bounded_above_of_compact_support hfs
  obtain ⟨C', hC', hsub⟩ := hLP n d hsep (tsupport f) hfs
  obtain ⟨A, -, hAI⟩ := hQI (GL (Fin n) ℂ) μ (twCent (thC n) d) ν C' hTc hC'
  have fin : ∀ g : GL (Fin n) ℂ → ℂ, Measurable g → (∀ t ∈ twCent (thC n) d, ∀ x, g (t * x) = g x) →
      (∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖g x‖ ≤ B) →
      Measurable (fun x => f (twConj (thC n) x d) * g x) ∧
      quotLIntegral μ (twCent (thC n) d) ν (fun x => ‖f (twConj (thC n) x d) * g x‖ₑ) ≠ ⊤ := by
    intro g hgm hgT hgb
    obtain ⟨Bg, hBg⟩ := hgb C' hC'
    have hm : Measurable (fun x => f (twConj (thC n) x d) * g x) := (hf.comp htc).measurable.mul hgm
    refine ⟨hm, (hAI _ (max Bf 0 * max Bg 0) (mul_nonneg (le_max_right _ _) (le_max_right _ _)) hm ?_ ?_ ?_).1⟩
    · intro t ht x
      rw [twConj_mul_left d t x ht, hgT t ht x]
    · intro x hx
      exact hsub (show twConj (thC n) x d ∈ tsupport f from
        subset_tsupport f (Function.mem_support.2 (left_ne_zero_of_mul hx)))
    · intro x hx
      rw [norm_mul]
      exact mul_le_mul ((hBf _).trans (le_max_left _ _)) ((hBg x hx).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)
  have goodsub : ∀ c c' : (Fin m → SignType) → ℝ, Measurable (fun x => V (p x + c) - V (p x + c')) ∧
      (∀ t ∈ twCent (thC n) d, ∀ x, V (p (t * x) + c) - V (p (t * x) + c') = V (p x + c) - V (p x + c')) ∧
      ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖V (p x + c) - V (p x + c')‖ ≤ B := by
    intro c c'
    obtain ⟨h1, h2, h3⟩ := good_V hV hL c
    obtain ⟨h1', h2', h3'⟩ := good_V hV hL c'
    refine ⟨h1.sub h1', fun t ht x => by rw [h2 t ht x, h2' t ht x], fun C hC => ?_⟩
    obtain ⟨B, hB⟩ := h3 C hC
    obtain ⟨B', hB'⟩ := h3' C hC
    exact ⟨B + B', fun x hx => (norm_sub_le _ _).trans (add_le_add (hB x hx) (hB' x hx))⟩
  have h0int : quotIntegral μ (twCent (thC n) d) ν (fun _ => (0 : ℂ)) = 0 := by
    simpa using (hQA (GL (Fin n) ℂ) μ (twCent (thC n) d) ν).2.2 0 (fun _ => 0)
  have main : ∀ s : Finset (Fin m → SignType), quotIntegral μ (twCent (thC n) d) ν
      (fun x => f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have h0 : zr z ∅ = 0 := by funext e; simp [zr]
      simp only [h0, sub_self, mul_zero]
      exact h0int
    · intro e s he ih
      have hFi := fin _ (goodsub (zr z (insert e s)) 0).1 (goodsub _ 0).2.1 (goodsub _ 0).2.2
      have hFs := fin _ (goodsub (zr z s) 0).1 (goodsub _ 0).2.1 (goodsub _ 0).2.2
      have hdiff : quotIntegral μ (twCent (thC n) d) ν
          (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + zr z s))) = 0 := by
        by_cases he0 : e = 0
        · subst he0
          have hzz : zr z (insert 0 s) = zr z s := by
            funext e'
            by_cases h : e' = 0
            · subst h; simp [zr, he, hz0]
            · simp [zr, h]
          simp only [hzz, sub_self, mul_zero]
          exact h0int
        · obtain ⟨W₁, W₂, ⟨hW1, hW12, hp1, hp2⟩, hnil⟩ := hL.nil e he0
          obtain ⟨hm, hTi, hb⟩ := goodsub (zr z (insert e s)) (zr z s)
          exact hLV n μ f (fun x => V (p x + zr z (insert e s)) - V (p x + zr z s)) d ν W₁ W₂ hf hfs hfc hsep
            hW1 hW12 hp1 hp2 hm hb (fun x k hk => by simp only [hL.cpt x k hk]) hTi
            (fun u hu x => diff_step hV z s e he _ _ (fun e' h => hnil u hu x e' h))
      have key : quotIntegral μ (twCent (thC n) d) ν
          (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + 0)) -
            f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) =
          quotIntegral μ (twCent (thC n) d) ν (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + 0))) -
          quotIntegral μ (twCent (thC n) d) ν (fun x => f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) :=
        (hQA (GL (Fin n) ℂ) μ (twCent (thC n) d) ν).2.1 _ _ hFi.1 hFs.1 hFi.2 hFs.2
      have hfun : (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + 0)) -
            f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) =
          fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + zr z s)) := by
        funext x; ring
      rw [hfun, hdiff, ih, sub_zero] at key
      exact key.symm
  have hu : zr z Finset.univ = z := by funext e; simp [zr]
  have := main Finset.univ
  rw [hu] at this
  simpa using this
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PQProd
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.QuotientProduct

theorem exists_haar_inv (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (hc : ∀ a b : H, a * b = b * a) : ∃ ν : Measure H, ν.IsHaarMeasure ∧ ν.IsInvInvariant := by
  let inst : CommGroup H := { (inferInstance : Group H) with mul_comm := hc }
  exact ⟨Measure.haar, inferInstance,
    @Measure.IsHaarMeasure.isInvInvariant_of_regular H inst _ _ _ _ Measure.haar _ _ _⟩

noncomputable def prodE {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
    (T₁ : Subgroup G₁) (T₂ : Subgroup G₂) : T₁ × T₂ ≃ₜ* T₁.prod T₂ :=
  _root_.UpperTheory.Reformulated.B.DaGva8.prodE T₁ T₂

def swapE (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂] :
    G₁ × G₂ ≃ₜ* G₂ × G₁ where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_swap
  continuous_invFun := continuous_swap

theorem isClosed_prod {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
    {T₁ : Subgroup G₁} {T₂ : Subgroup G₂} (h₁ : IsClosed (T₁ : Set G₁)) (h₂ : IsClosed (T₂ : Set G₂)) :
    IsClosed ((T₁.prod T₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) := by
  rw [Subgroup.coe_prod]; exact h₁.prod h₂

theorem left (hQP : PositivityTheory.Rg.BcB.D4.QuotProd) (hQM : QMap)
    (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁]
    [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (G₂ : Type) [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂]
    [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure]
    (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
    (T₁ : Subgroup G₁) (T₂ : Subgroup G₂) (ν : Measure (T₁.prod T₂)) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    (F : G₁ × G₂ → ℂ) (hT₁ : IsClosed (T₁ : Set G₁)) (hT₂ : IsClosed (T₂ : Set G₂))
    (hc₁ : ∀ s ∈ T₁, ∀ t ∈ T₁, s * t = t * s) (hc₂ : ∀ s ∈ T₂, ∀ t ∈ T₂, s * t = t * s)
    (hF : Measurable F) (hFT : ∀ t ∈ T₁.prod T₂, ∀ x, F (t * x) = F x)
    (h : ∀ (ν₁ : Measure T₁) [ν₁.IsHaarMeasure] [ν₁.IsInvInvariant] x₂,
      quotIntegral μ₁ T₁ ν₁ (fun x₁ => F (x₁, x₂)) = 0) :
    quotIntegral (μ₁.prod μ₂) (T₁.prod T₂) ν F = 0 := by
  have : LocallyCompactSpace T₁ := hT₁.locallyCompactSpace
  have : LocallyCompactSpace T₂ := hT₂.locallyCompactSpace
  have : SecondCountableTopology T₁ := inferInstanceAs (SecondCountableTopology (T₁ : Set G₁))
  have : SecondCountableTopology T₂ := inferInstanceAs (SecondCountableTopology (T₂ : Set G₂))
  obtain ⟨ν₁, _, _⟩ := exists_haar_inv T₁ (fun a b => Subtype.ext (hc₁ a a.2 b b.2))
  obtain ⟨ν₂, _, _⟩ := exists_haar_inv T₂ (fun a b => Subtype.ext (hc₂ a a.2 b b.2))
  set E := prodE T₁ T₂
  have hE : Measurable E := E.continuous.measurable
  have hinvP : Measure.map Inv.inv (ν₁.prod ν₂) = ν₁.prod ν₂ := by
    have : (Inv.inv : T₁ × T₂ → T₁ × T₂) = Prod.map Inv.inv Inv.inv := rfl
    rw [this, ← Measure.map_prod_map _ _ continuous_inv.measurable continuous_inv.measurable,
      Measure.map_inv_eq_self, Measure.map_inv_eq_self]
  have : (Measure.map E (ν₁.prod ν₂)).IsInvInvariant := by
    constructor
    show Measure.map Inv.inv (Measure.map E (ν₁.prod ν₂)) = Measure.map E (ν₁.prod ν₂)
    rw [Measure.map_map continuous_inv.measurable hE]
    have : (Inv.inv ∘ ⇑E) = ⇑E ∘ Inv.inv := funext fun p => (map_inv E p).symm
    rw [this, ← Measure.map_map hE continuous_inv.measurable, hinvP]
  have hmap : (Measure.map E (ν₁.prod ν₂)).map
      (fun t : T₁.prod T₂ => ((⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩) : T₁ × T₂)) =
      ν₁.prod ν₂ := by
    have : (fun t : T₁.prod T₂ => ((⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩) : T₁ × T₂))
      = ⇑E.symm := rfl
    rw [this, Measure.map_map (show Measurable ⇑E.symm from E.symm.continuous.measurable) hE]
    have : (⇑E.symm ∘ ⇑E) = id := funext fun p => E.symm_apply_apply p
    rw [this, Measure.map_id]
  have h0 := hQP G₁ G₂ μ₁ μ₂ T₁ T₂ ν₁ ν₂ (Measure.map E (ν₁.prod ν₂)) F hF hmap hFT (fun x₂ => h ν₁ x₂)
  refine hQM (G₁ × G₂) (G₁ × G₂) (ContinuousMulEquiv.refl _) (μ₁.prod μ₂) (μ₁.prod μ₂) (T₁.prod T₂) (T₁.prod T₂)
    ν (Measure.map E (ν₁.prod ν₂)) F (isClosed_prod hT₁ hT₂) ?_ hF hFT h0
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨x, hx, rfl⟩

end PositivityTheory.Rg.BcB.CV.QuotientProduct

namespace PositivityTheory.Rg.BcB.CV

open QuotientProduct in
theorem pf_QProd : PositivityTheory.Rg.BcB.D4.QuotProd → PositivityTheory.Rg.BcB.CV.QMap → PositivityTheory.Rg.BcB.CV.QProd := by
  intro hQP hQM G₁ _ _ _ _ _ _ _ _ G₂ _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ T₁ T₂ ν _ _ F hT₁ hT₂ hc₁ hc₂ hF hFT hcase
  rcases hcase with h | h
  · exact left hQP hQM G₁ G₂ μ₁ μ₂ T₁ T₂ ν F hT₁ hT₂ hc₁ hc₂ hF hFT h
  · have hcl := isClosed_prod hT₂ hT₁
    have : LocallyCompactSpace (T₂.prod T₁) := hcl.locallyCompactSpace
    have : SecondCountableTopology (T₂.prod T₁) :=
      inferInstanceAs (SecondCountableTopology ((T₂.prod T₁ : Subgroup (G₂ × G₁)) : Set (G₂ × G₁)))
    obtain ⟨ν', _, _⟩ := exists_haar_inv (T₂.prod T₁) (fun a b => Subtype.ext (Prod.ext
      (hc₂ _ (Subgroup.mem_prod.1 a.2).1 _ (Subgroup.mem_prod.1 b.2).1)
      (hc₁ _ (Subgroup.mem_prod.1 a.2).2 _ (Subgroup.mem_prod.1 b.2).2)))
    set S := swapE G₁ G₂
    have hFT' : ∀ t ∈ T₂.prod T₁, ∀ x, F (S.symm (t * x)) = F (S.symm x) := by
      intro t ht x
      rw [map_mul]
      exact hFT _ (Subgroup.mem_prod.2 ⟨(Subgroup.mem_prod.1 ht).2, (Subgroup.mem_prod.1 ht).1⟩) _
    have h0 := left hQP hQM G₂ G₁ μ₂ μ₁ T₂ T₁ ν' (fun y => F (S.symm y)) hT₂ hT₁ hc₂ hc₁
      (hF.comp S.symm.continuous.measurable) hFT' (fun ν₂ _ _ x₁ => h ν₂ x₁)
    refine hQM (G₁ × G₂) (G₂ × G₁) S (μ₁.prod μ₂) (μ₂.prod μ₁) (T₁.prod T₂) (T₂.prod T₁)
      ν ν' F (isClosed_prod hT₁ hT₂) ?_ hF hFT h0
    ext ⟨a, b⟩
    simp only [Subgroup.mem_map, Subgroup.mem_prod]
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩
      change (y, x) = (a, b) at hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨hy, hx⟩
    · rintro ⟨ha, hb⟩
      exact ⟨(b, a), ⟨hb, ha⟩, rfl⟩

end PositivityTheory.Rg.BcB.CV
end
end

