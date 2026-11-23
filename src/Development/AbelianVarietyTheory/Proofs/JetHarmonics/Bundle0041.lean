module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0004
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BlockHarmLevOfBlockHarm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0002
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntChartFrTrunc
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntChartTrunc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.L2.Pj.SaturatedCharts (toT prodPts_of_combAt combAt_of_prodPts chartTan_of tanAt_of isTan_iff' fst_comp_jetTan)

attribute [local instance] Over.cartesianMonoidalCategory


set_option maxHeartbeats 1000000 in
open ReciprocityTheory.ChartRestriction.G.Chart (tcoord) in
theorem exists_intChart_frTrunc : IntChartStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ChartTransportSt Xo c → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT := by
  intro hIC E _ _ _ H Dw l Xo c _ hstar hTr T io y
  have I : IntData Xo c T io y.1 := Classical.choice (by
    obtain ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩ := y.2.2
    exact ⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩⟩)

  have hp1 : IsProper I.t'.G.hom := by
    have := Xo.univ.proper
    rw [← I.m1.cart.1.isoPullback_hom_snd]
    infer_instance
  have hprop : IsProper ((Over.pullback (spMap (algebraMap T.V (FractionRing T.V)))).obj I.G.G).hom := by
    show IsProper (pullback.snd I.G.G.hom (spMap (algebraMap T.V T.Fr)))
    rw [← I.m2.cart.1.isoPullback_inv_snd]
    infer_instance

  have hsm : Smooth I.G.G.hom := I.G.semi.smooth
  obtain ⟨n, x, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc (R := T.V) I.G.G
  let v : Fin n → (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := T.V) (DualNumber T.V) ⟶ I.G.G) := fun i =>
    ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := x) (Pi.single i 1)
  let tg : Fin n → (Sp (DualNumber T.V) ⟶ I.G.G.left) := fun i => (v i).left
  have htgo : ∀ i, tg i ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := fun i => Over.w (v i)
  have htgt : ∀ i, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT I.G (tg i) (htgo i)) := fun i =>
    ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx _
  have htgc : ∀ i, tcoord hx _ (htgt i) = Pi.single i 1 := fun i => ReciprocityTheory.ChartRestriction.G.Chart.tcoord_tvec hx _
  have htan : ∀ i, IsTanAtG I.G (𝟙 (Sp T.V)) (tg i) := fun i => tanAt_of I.G _ (htgo i) (htgt i)
  let e0 := Fintype.equivFin (Fin n)

  have hcombR : ∀ (a : Fin (Fintype.card (Fin n)) → T.V) (w : Sp (DualNumber T.V) ⟶ I.G.G.left)
      (hw : w ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V))),
      IsCombAtG I.G (𝟙 (Sp T.V)) (fun j => tg (e0.symm j)) a w ↔
        ∃ h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT I.G w hw), tcoord hx _ h = fun i => a (e0 i) := by
    intro a w hw
    rw [combAt_iff I.G hx (fun j => tg (e0.symm j)) (fun j => htgo _) (fun j => htgt _) a w hw]
    have hs : ∑ j, a j • tcoord hx _ (htgt (e0.symm j)) = fun i => a (e0 i) := by
      simp only [htgc]
      rw [← Equiv.sum_comp e0 (fun j => a j • (Pi.single (e0.symm j) (1 : T.V) : Fin n → T.V))]
      simp only [Equiv.symm_apply_apply]
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hs]
  have hwo : ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → w ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) :=
    fun w hw => hw.1.trans (Category.comp_id _)
  have hbasR : ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w →
      ∃! a : Fin (Fintype.card (Fin n)) → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) (fun j => tg (e0.symm j)) a w := by
    intro w hw
    have ht := chartTan_of I.G w hw
    refine ⟨fun j => tcoord hx _ ht (e0.symm j), (hcombR _ w (hwo w hw)).2 ⟨ht, ?_⟩, fun a ha => ?_⟩
    · funext i
      simp only [Equiv.symm_apply_apply]
    · obtain ⟨h', hh'⟩ := (hcombR a w (hwo w hw)).1 ha
      funext j
      have := congrFun hh' (e0.symm j)
      simp only [Equiv.apply_symm_apply] at this
      rw [← this]
  have hbas : ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w →
      ∃! a : Fin n → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) (m := Fintype.card (Fin n))
        (fun i => tg (e0.symm i)) (fun i => a (e0.symm i)) w := by
    intro w hw
    obtain ⟨a, ha, hu⟩ := hbasR w hw
    refine ⟨fun i => a (e0 i), by simpa only [Equiv.apply_symm_apply] using ha, fun b hb => ?_⟩
    have := hu _ hb
    funext i
    rw [← this]
    simp only [Equiv.symm_apply_apply]

  obtain ⟨d, B, uvec, xT, eT, wPT, hd, hu, hch, hfr, hpr, htr, hrig, -⟩ :=
    hIC E H T.V inferInstance I.G hprop tg htan hbas hstar
  subst hd
  let tgT : Fin (Fintype.card (Fin n)) → (Sp (DualNumber T.V) ⟶ I.G.G.left) := fun j => tg (e0.symm j)
  have chartT : IsChartG I.G (𝟙 (Sp T.V)) (Fintype.card (Fin n)) B.G.F B.A.act tgT
      (fun j => Pi.single j (1 : T.V)) xT := by
    have h0 := isChartG_reindex I.G (𝟙 (Sp T.V)) _ B.G.F B.A.act tg uvec xT hch e0.symm
    have hue : (fun ℓ => uvec (e0.symm ℓ)) = fun j => Pi.single j (1 : T.V) := by
      funext ℓ j
      rw [hu, Equiv.apply_symm_apply, Pi.single_apply]
      simp only [Fin.val_inj, eq_comm]
    rw [hue] at h0
    exact h0
  have tgBasis : (∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin (Fintype.card (Fin n)) → T.V,
        IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w := ⟨fun j => htan _, hbasR⟩

  have hDo : ∀ j, (homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) :
      Jet T.V (Fin 1 × Fin (Fintype.card (Fin n))) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left ≫ I.G.G.hom =
        spMap (algebraMap T.V (DualNumber T.V)) := fun j =>
    (Over.w (homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) :
      Jet T.V (Fin 1 × Fin (Fintype.card (Fin n))) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1)).trans
      (Category.comp_id _)
  have hDt := fun j => dir_tan I.G xT chartT.zero j (hDo j)
  have hDc : ∀ j, tcoord hx _ (hDt j) = tcoord hx _ (htgt (e0.symm j)) := by
    intro j
    obtain ⟨h, hh⟩ := (combAt_iff I.G hx _ hDo hDt (Pi.single j 1) (tgT j) (htgo _)).1 (chartT.tan j)
    rw [ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx rfl (htgt _) h, hh]
    simp [Pi.single_apply]

  have hubo : ∀ ℓ : Lt1 Dw, (I.ub ℓ.1 ℓ.2).left ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) :=
    fun ℓ => Over.w _
  have hubt : ∀ ℓ : Lt1 Dw, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT I.G _ (hubo ℓ)) := fun ℓ =>
    (isTan_iff' I.G _).1 (I.tan ℓ.1 ℓ.2)
  let uvecT : Lt1 Dw → Fin (Fintype.card (Fin n)) → T.V := fun ℓ j => tcoord hx _ (hubt ℓ) (e0.symm j)
  have dirT : ∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin (Fintype.card (Fin n)) => (homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (Fintype.card (Fin n))) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫
          xT 1).left) (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left := by
    intro ℓ
    refine (combAt_iff I.G hx _ hDo hDt (uvecT ℓ) _ (hubo ℓ)).2 ⟨hubt ℓ, ?_⟩
    simp only [hDc, htgc, uvecT]
    rw [← Equiv.sum_comp e0 (fun j => tcoord hx _ (hubt ℓ) (e0.symm j) •
      (Pi.single (e0.symm j) (1 : T.V) : Fin n → T.V))]
    simp only [Equiv.symm_apply_apply]
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨B', uvec', x', e', wP', h', hch', hfr', hpr', hg', hr', hgen⟩ :=
    hTr hstar T io y I _ B tgT uvecT xT eT wPT tgBasis chartT dirT hfr hpr htr hrig
  letI := io.toAlgebra
  exact ⟨⟨⟨_, B', uvec', x', e', wP', h', hch', hfr', hpr', hg', hr'⟩, I, B.G.F, B.A.act, B.ph1, B.ph2, B.sy, B.ad,
    uvecT, tgT, xT, eT, wPT, tgBasis, chartT, dirT, hfr, hpr, hgen⟩, htr⟩

end GlobalTheory.IntChartTrunc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsBetaUnitBlock
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BetaOfSum

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BetaEx GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility GlobalTheory.ShortLawsCompare

section Lattice

variable {E : Type} [Field E] [NumberField E] {n₁ n₂ : ℕ}

theorem mem_block (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E))
    (v : Fin (n₁ + n₂) → E) : v ∈ (blockLat ⟨M₁⟩ ⟨M₂⟩).La ↔
      (fun i => v (Fin.castAdd n₂ i)) ∈ M₁ ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ M₂ := Iff.rfl


omit [NumberField E] in
theorem det_block (u : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) E)
    (h : ∀ i j, u (Fin.castAdd n₂ i) (Fin.natAdd n₁ j) = 0) :
    u.det = (Matrix.of fun i j => u (Fin.castAdd n₂ i) (Fin.castAdd n₂ j)).det *
      (Matrix.of fun i j => u (Fin.natAdd n₁ i) (Fin.natAdd n₁ j)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, ← Matrix.det_fromBlocks_zero₁₂ _
    (Matrix.of fun i j => u (Fin.natAdd n₁ i) (Fin.castAdd n₂ j))]
  congr 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [h]


omit [NumberField E] in
theorem det_pure_mem (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E))
    (w : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) E)
    (h₁ : ∀ i, (fun j => w i (Fin.castAdd n₂ j)) ∈ M₁) (h₂ : ∀ i, (fun j => w i (Fin.natAdd n₁ j)) ∈ M₂)
    (h : ∀ i, (∀ j, w i (Fin.castAdd n₂ j) = 0) ∨ ∀ j, w i (Fin.natAdd n₁ j) = 0) :
    w.det ∈ detSpan M₁ * detSpan M₂ := by
  by_cases h0 : w.det = 0
  · rw [h0]; exact zero_mem _
  have h0' := h0
  rw [Matrix.det_apply] at h0'
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0'
  have hd : ∀ i, w (σ i) i ≠ 0 := fun i hi => hσ (by
    rw [Finset.prod_eq_zero (f := fun k => w (σ k) k) (Finset.mem_univ i) hi, smul_zero])
  have hm : (w.submatrix σ id).det ∈ detSpan M₁ * detSpan M₂ := by
    rw [det_block _ (fun i j => ((h (σ (Fin.castAdd n₂ i))).resolve_left fun g => hd _ (g i)) j)]
    exact Submodule.mul_mem_mul (det_mem _ fun i => h₁ _) (det_mem _ fun i => h₂ _)
  rw [Matrix.det_permute] at hm
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> rw [e] at hm
  · simpa using hm
  · simpa using hm

theorem detSpan_block (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E)) :
    detSpan (blockLat ⟨M₁⟩ ⟨M₂⟩).La = detSpan M₁ * detSpan M₂ := by
  classical
  have z₁ : (fun _ => 0) ∈ M₁ := M₁.zero_mem
  have z₂ : (fun _ => 0) ∈ M₂ := M₂.zero_mem
  apply le_antisymm
  · refine Submodule.span_le.2 fun d hd => ?_
    obtain ⟨v, hv, rfl⟩ := (mem_detSet _ d).1 hd
    let a : Fin (n₁ + n₂) → Fin (n₁ + n₂) → E := fun i => Fin.append (fun j => v i (Fin.castAdd n₂ j)) 0
    let b : Fin (n₁ + n₂) → Fin (n₁ + n₂) → E := fun i => Fin.append 0 (fun j => v i (Fin.natAdd n₁ j))
    have e : (v : Fin (n₁ + n₂) → Fin (n₁ + n₂) → E) = a + b := by
      funext i j
      induction j using Fin.addCases <;> simp [a, b]
    have e2 : v.det = ∑ s : Finset (Fin (n₁ + n₂)), (Matrix.of (s.piecewise a b)).det := by
      have := (Matrix.detRowAlternating (n := Fin (n₁ + n₂)) (R := E)).toMultilinearMap.map_add_univ a b
      rw [← e] at this
      exact this
    rw [SetLike.mem_coe, e2]
    refine Submodule.sum_mem _ fun s _ => det_pure_mem M₁ M₂ _ (fun i => ?_) (fun i => ?_) (fun i => ?_)
    · by_cases hi : i ∈ s
      · simpa [hi, a] using ((mem_block _ _ _).1 (hv i)).1
      · simpa [hi, b] using z₁
    · by_cases hi : i ∈ s
      · simpa [hi, a] using z₂
      · simpa [hi, b] using ((mem_block _ _ _).1 (hv i)).2
    · by_cases hi : i ∈ s
      · exact Or.inr fun j => by simp [hi, a]
      · exact Or.inl fun j => by simp [hi, b]
  · rw [detSpan, detSpan, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (mem_detSet _ _).1 hx
    obtain ⟨w, hw, rfl⟩ := (mem_detSet _ _).1 hy
    let u : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) E :=
      Matrix.of (Fin.append (fun i => Fin.append (v i) 0) (fun i => Fin.append 0 (w i)))
    have e : u.det = v.det * w.det := by
      rw [det_block u (fun i j => by simp [u])]
      congr 2 <;> ext i j <;> simp [u]
    change v.det * w.det ∈ detSpan _
    rw [← e]
    refine det_mem _ fun i => (mem_block _ _ _).2 ?_
    induction i using Fin.addCases with
    | left i => exact ⟨by simpa [u] using hv i, by simpa [u] using z₂⟩
    | right i => exact ⟨by simpa [u] using z₁, by simpa [u] using hw i⟩

theorem block_Ln (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) :
    (blockLat Λ₁ Λ₂).Ln = (blockLat ⟨Λ₁.Ln⟩ ⟨Λ₂.Ln⟩).La := by
  ext v
  change (v ∈ (blockLat Λ₁ Λ₂).La ∧ v ∈ stdLat E _) ↔ _
  rw [mem_std_block, mem_block, mem_block]
  exact and_and_and_comm

theorem index_block (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) :
    ((blockLat Λ₁ Λ₂).Ln.toAddSubgroup.addSubgroupOf (blockLat Λ₁ Λ₂).La.toAddSubgroup).index =
      (Λ₁.Ln.toAddSubgroup.addSubgroupOf Λ₁.La.toAddSubgroup).index *
        (Λ₂.Ln.toAddSubgroup.addSubgroupOf Λ₂.La.toAddSubgroup).index := by
  let φ : (blockLat Λ₁ Λ₂).La.toAddSubgroup →+ Λ₁.La.toAddSubgroup × Λ₂.La.toAddSubgroup :=
    { toFun := fun v => (⟨fun i => v.1 (Fin.castAdd n₂ i), v.2.1⟩, ⟨fun j => v.1 (Fin.natAdd n₁ j), v.2.2⟩)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨⟨Fin.append x y, (mem_block _ _ _).2 ⟨by simpa using hx, by simpa using hy⟩⟩, ?_⟩
    ext j <;> simp [φ]
  rw [← AddSubgroup.index_prod, ← AddSubgroup.index_comap_of_surjective _ hφ, block_Ln]
  rfl

end Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n₁ n₂ : ℕ}

theorem idealAt_block (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E)) (τ : E →+* ℂ) :
    idealAt c (blockLat ⟨M₁⟩ ⟨M₂⟩).La τ = idealAt c M₁ τ * idealAt c M₂ τ := by
  have e := detSpan_block M₁ M₂
  unfold detSpan at e
  unfold idealAt
  rw [← span_image_span, e, Submodule.span_mul_span, span_image_span, Submodule.span_mul_span, Set.image_mul]

theorem isBeta_block {Λ₁ : GenLat E n₁} {Λ₂ : GenLat E n₂} {β₁ β₂ : c.F} (b₁ : IsBeta Dw c Λ₁ β₁)
    (b₂ : IsBeta Dw c Λ₂ β₂) : IsBeta Dw c (blockLat Λ₁ Λ₂) (β₁ * β₂) := by
  refine ⟨mul_ne_zero b₁.1 b₂.1, ?_, fun σ => ?_⟩
  · have e₁ := b₁.2.1
    have e₂ := b₂.2.1
    unfold BetaIs at e₁ e₂ ⊢
    rw [block_Ln]
    simp only [idealAt_block c Λ₁.La Λ₂.La, idealAt_block c Λ₁.Ln Λ₂.Ln, mul_pow, Finset.prod_mul_distrib]
    rw [← e₁, ← e₂, ← Set.singleton_mul_singleton, ← Submodule.span_mul_span, mul_mul_mul_comm]
  · rw [index_block, map_mul, norm_mul, mul_pow, b₁.2.2 σ, b₂.2.2 σ, Nat.cast_mul, mul_pow]

theorem isBeta_unit_block (n₁ : ℕ) (Λ₂ : GenLat E n₂) (β : c.F) :
    IsBeta Dw c (blockLat (unitLat E n₁) Λ₂) β ↔ IsBeta Dw c Λ₂ β := by
  have e : (unitLat E n₁).Ln = (unitLat E n₁).La := inf_idem _
  have hu : IsUnit (∏ τ : E →+* ℂ, idealAt c (unitLat E n₁).La τ ^ Dw.mult τ) :=
    IsUnit.prod_univ_iff.2 fun τ =>
      (isUnit_idealAt c (trivAt_std n₁ 0) (unimod_std n₁) zero_ne_one τ).pow _
  refine and_congr_right fun _ => and_congr ?_ (forall_congr' fun σ => ?_)
  · unfold BetaIs
    rw [block_Ln, e]
    simp only [idealAt_block c (unitLat E n₁).La Λ₂.La, idealAt_block c (unitLat E n₁).La Λ₂.Ln, mul_pow,
      Finset.prod_mul_distrib]
    rw [mul_left_comm, hu.mul_right_inj]
  · rw [index_block, e]
    simp

theorem blockBeta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (bad : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.BlockBeta Dw c bad := by
  intro E _ _ _ H Dw l c bad
  refine ⟨fun n₁ n₂ Λ₁ Λ₂ h₁ h₂ β₁ β₂ β b₁ b₂ => ⟨fun b => ?_, ?_⟩,
    fun n₁ n₂ Λ₂ _ => ⟨GlobalTheory.Survey.BaseClassMove.isBeta_unit c n₁, isBeta_unit_block c n₁ Λ₂⟩⟩
  · have hB := latOK_block h₁ h₂
    exact isBeta_ratio c hB.1 hB.2.2 (isBeta_block c b₁ b₂) b
  · rintro ⟨ζ, hζ, rfl⟩
    exact isBeta_mul c (isBeta_block c b₁ b₂) hζ

end GlobalTheory.BetaOfSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelCoverDatumSimilitudeAdjointTransportStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCoverDatum_similitude_adjoint_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.l₂.M = l.M * d.pd → d.l₂.Mb = l.Mb * d.I → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ g : Sim Dw, (∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 E) Dw.La)) → ∃ σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f d.l₂.M a)) ∧ ∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → ∃ x0' : Fin n → Dw.La, AdmX (l := l) rk x0' ∧ ∀ q : Fin n → LevQ Dw d.l₂, d.w x0 (fun b => σq.symm (q b)) = d.w x0' q := by
  first | exact @GlobalTheory.DatumCoverAdjoint.datum_adjoint | exact GlobalTheory.DatumCoverAdjoint.datum_adjoint | (intros; apply GlobalTheory.DatumCoverAdjoint.datum_adjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SigmaFiniteOfPosLintegralNeTop
section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.QuotientMeasureSigmaFinite

theorem sigmaFinite_of_pos_lintegral_ne_top {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {g : X → ℝ≥0∞} (hg : Measurable g) (hpos : ∀ x, g x ≠ 0) (hfin : ∫⁻ x, g x ∂ν ≠ ∞) :
    SigmaFinite ν := by
  refine Measure.sigmaFinite_of_countable (S := Set.range fun n : ℕ => {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨n, rfl⟩
    have h0 : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
    have h1 : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
    exact (meas_ge_le_lintegral_div hg.aemeasurable h0 h1).trans_lt (ENNReal.div_lt_top hfin h0)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hpos x)
    refine Set.mem_sUnion.2 ⟨_, ⟨n, rfl⟩, ?_⟩
    show ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x
    exact le_trans (ENNReal.inv_le_inv.2 le_self_add) hn.le

theorem measurable_mul_pair (k r : ℕ) :
    Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt k r)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem sigmaFinite_of_isQuotMeas {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    [SigmaFinite μG] [SFinite μS] (hS : μS ≠ 0)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS ν) : SigmaFinite ν := by
  obtain ⟨h, hpos, hmeas, hint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  have hne : ∀ y, h y ≠ 0 := fun y => (hpos y).ne'
  have hF : Measurable fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ((h (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j) : NNReal) : ℝ≥0∞) :=
    (measurable_coe_nnreal_ennreal.comp hmeas).comp (measurable_mul_pair k r)
  have hq' : ∫⁻ x, (h x : ℝ≥0∞) ∂μG =
      ∫⁻ x, (∫⁻ s, (h (fun i j => (Matrix.of s * Matrix.of x) i j) : ℝ≥0∞) ∂μS) ∂ν :=
    hq _ (measurable_coe_nnreal_ennreal.comp hmeas)

  refine sigmaFinite_of_pos_lintegral_ne_top
    (g := fun x => ∫⁻ s, (h (fun i j => (Matrix.of s * Matrix.of x) i j) : ℝ≥0∞) ∂μS)
    hF.lintegral_prod_right' ?_ ?_
  · intro x hx
    have hfm : Measurable fun s : Formalism.QuantumDeterminants.Mt k r =>
        ((h (fun i j => (Matrix.of s * Matrix.of x) i j) : NNReal) : ℝ≥0∞) :=
      (measurable_coe_nnreal_ennreal.comp hmeas).comp
        (Measurable.of_eval fun i => Measurable.of_eval fun j => by
          simp only [Matrix.mul_apply, Matrix.of_apply]
          fun_prop)
    rw [lintegral_eq_zero_iff hfm] at hx
    apply hS
    rw [← Measure.measure_univ_eq_zero]
    have h0 := ae_iff.1 hx
    simpa [hne] using h0
  · rw [← hq']
    exact (hint.trans ENNReal.one_lt_top).ne

end GlobalTheory.QuotientMeasureSigmaFinite
end

