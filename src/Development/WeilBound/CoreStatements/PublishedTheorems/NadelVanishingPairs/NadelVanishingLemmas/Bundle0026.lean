module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0015
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsEmbeddedResolution
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogResStep


open GlobalTheory.Cartier.CartierDiv in
theorem supp_neg_le {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) : (-D).supp ≤ D.supp := fun x hx h =>
  hx (by simpa using h.neg)

theorem supp_nsmul_le {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (m : ℕ) : (m • D).supp ≤ D.supp := by
  induction m with
  | zero => simp [(CartierDiv.supp_eq_bot_iff (D := (0 : CartierDiv X))).2 rfl]
  | succ m ih => exact (succ_nsmul D m ▸ CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

theorem sup_ne_top {Y : Scheme.{0}} [IsIntegral Y] {Z W : Closeds Y} (hZ : Z ≠ ⊤) (hW : W ≠ ⊤) : Z ⊔ W ≠ ⊤ := by
  have key : ∀ C : Closeds Y, C ≠ ⊤ → genericPoint Y ∉ C := fun C hC h => hC <| by
    ext x; simp only [Closeds.coe_top, Set.mem_univ, iff_true]
    exact ((genericPoint_spec Y).mem_closed_set_iff C.isClosed).1 h (Set.mem_univ x)
  intro h
  have : genericPoint Y ∈ Z ⊔ W := by rw [h]; trivial
  rcases this with h' | h'
  · exact key Z hZ h'
  · exact key W hW h'

end GlobalTheory.LogResStep

open GlobalTheory.LogResStep in
theorem GlobalTheory.exists_logRes_ample : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X), η ≠ 0 → ∀ (Y₀ : Scheme.{0}) [IsIntegral Y₀] (s₀ : Y₀ ⟶ X) [IsDominant s₀], SmoothOfRelativeDimension n (s₀ ≫ p) → IsProjOver (s₀ ≫ p) → Function.Bijective (functionFieldMap s₀) → ∀ (Z : Closeds Y₀), Z ≠ ⊤ → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (t : Y ⟶ Y₀) (_ : IsDominant t) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G (t ≫ s₀) K B ∧ (∀ y, t y ∈ Z → y ∈ B) ∧ ∃ (c : ℕ) (E : CartierDiv Y) (A₁ : LB Y) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ B ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  intro hP k _ _ X _ p n η m G hη Y₀ _ s₀ _ hsm hproj hbij Z hZ A hA
  haveI : SmoothOfRelativeDimension n (s₀ ≫ p) := hsm
  haveI : Smooth (s₀ ≫ p) := SmoothOfRelativeDimension.smooth n _
  haveI : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian (s₀ ≫ p)

  set η₀ := EtaleKlt.ratPull p s₀ n η with hη₀def
  have hη₀ : η₀ ≠ 0 := fun h =>
    hη ((_root_.GlobalTheory.EtaleKlt.ratPull_bijective_of_birational k X Y₀ p s₀ hbij n).1 (h.trans (map_zero _).symm))
  obtain ⟨K₀, hK₀⟩ := (GlobalTheory.T.canonical_divisor_of_form k Y₀ (s₀ ≫ p) n η₀ hη₀).1

  set D₀ : CartierDiv Y₀ := pullCart s₀ G - m • K₀ with hD₀
  set Z' : Closeds Y₀ := Z ⊔ D₀.supp with hZ'
  have hZ'top : Z' ≠ ⊤ := sup_ne_top hZ D₀.supp_ne_top
  set I : Y₀.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z' with hIdef
  have hIsupp : (I.support : Set Y₀) = Z' := Scheme.IdealSheafData.coe_support_vanishingIdeal Z'
  have hI : I ≠ ⊥ := by
    intro h
    apply hZ'top
    ext x
    rw [← hIsupp, h]
    simp
  obtain ⟨Y, t, hYi, hsmY, hprojY, -, hiso, heff, hsnc⟩ := hP k n Y₀ (s₀ ≫ p) inferInstance hsm hproj I hI
  haveI := hYi
  have hne := Principalise.nonempty_compl_support hI
  haveI : IsDominant t := GlobalTheory.T.isDominant_of_isIso_restrict' Y₀ Y t I.support.compl hne hiso
  haveI : SmoothOfRelativeDimension n (t ≫ s₀ ≫ p) := hsmY
  haveI : SmoothOfRelativeDimension n ((t ≫ s₀) ≫ p) := by rw [Category.assoc]; exact hsmY
  haveI : Smooth (t ≫ s₀ ≫ p) := SmoothOfRelativeDimension.smooth n _
  have hsmY' : SmoothOfRelativeDimension n ((t ≫ s₀) ≫ p) := by rw [Category.assoc]; exact hsmY
  have hprojY' : IsProjOver ((t ≫ s₀) ≫ p) := by rw [Category.assoc]; exact hprojY
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (t ≫ s₀ ≫ p)
  have hcomp := GlobalTheory.T.pullback_composition_compatible k X Y₀ Y p s₀ t
  have hbt := _root_.GlobalTheory.Discrepancy.functionFieldMap_bijective_of_isIso_restrict Y₀ Y t I.support.compl hne hiso
  have hbij' : Function.Bijective (functionFieldMap (t ≫ s₀)) := by
    rw [hcomp.1, RingHom.coe_comp]; exact hbt.comp hbij
  have hη₁ : EtaleKlt.ratPull p (t ≫ s₀) n η ≠ 0 := fun h =>
    hη ((_root_.GlobalTheory.EtaleKlt.ratPull_bijective_of_birational k X Y p (t ≫ s₀) hbij' n).1 (h.trans (map_zero _).symm))
  obtain ⟨K, hK⟩ := (GlobalTheory.T.canonical_divisor_of_form k Y ((t ≫ s₀) ≫ p) n _ hη₁).1
  have hK' : IsDivOfForm K (EtaleKlt.ratPull (s₀ ≫ p) t n η₀) := ((hcomp.2.2 n η K).1 hK)

  have hB : ∀ y : Y, y ∈ (I.comap t).support ↔ t y ∈ Z' := fun y => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap]
    change t y ∈ (I.support : Set Y₀) ↔ _
    rw [hIsupp]; rfl
  have hkiso := GlobalTheory.T.canonical_divisor_birational_compare k Y₀ Y (s₀ ≫ p) n t I.support.compl hne hiso η₀ hη₀ K₀ K hK₀ hK'
  have heq : pullCart (t ≫ s₀) G - m • K = pullCart t D₀ + m • (-(K - pullCart t K₀)) := by
    rw [hcomp.2.1 G, hD₀]
    change _ = pullCartHom t (pullCart s₀ G - m • K₀) + _
    rw [map_sub, map_nsmul]
    change _ = pullCart t (pullCart s₀ G) - m • pullCart t K₀ + _
    rw [smul_neg, nsmul_sub]; abel
  refine ⟨Y, hYi, t, inferInstance, K, (I.comap t).support,
    ⟨hsmY', hprojY', hbij', hK, hsnc, ?_⟩, ?_, ?_⟩
  · rw [heq]
    refine (CartierDiv.supp_add_le _ _).trans (sup_le ?_ ?_)
    · intro y hy
      rw [hB]
      exact Or.inr ((_root_.GlobalTheory.Discrepancy.pullCart_supp_and_eff Y₀ Y t D₀).1 y hy)
    · intro y hy
      have hy' := supp_neg_le _ (supp_nsmul_le _ m hy)
      rw [hB]
      by_contra hc
      refine hkiso y ?_ hy'
      intro hm
      have : t y ∈ (I.support : Set Y₀) := hm
      rw [hIsupp] at this; exact hc this
  · intro y hy; rw [hB]; exact Or.inl hy
  · exact GlobalTheory.T.blowup_ample_relative k Y₀ Y (s₀ ≫ p) n t hproj hprojY I hiso heff A hA
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegVanishing
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair

namespace GlobalTheory.Div

theorem vanishing_ample_snc_charZero : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f], IsProjOver f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  intro k _ _ X f d _ hproj s L σ h K M A hM hA r b hr hb hcls q hq
  have hprop : IsProper f := GlobalTheory.SchemeWords.isProper_of_isProjOver hproj
  obtain ⟨R, X₁, f₁, π, L₁, σ₁, h₁, M₁, hM₁, hft, hprop₁, hpb, hL, hMc⟩ :=
    GlobalTheory.T.spread_out_relative_snc k X f d hprop s L σ h M hM
  haveI : SmoothOfRelativeDimension d f₁ := _root_.GlobalTheory.LogPair.smooth_of_relSnc R X₁ f₁ d s L₁ σ₁ h₁
  haveI : IsProper f₁ := hprop₁
  obtain ⟨K₁⟩ := (CanonLB.nonempty : Nonempty (CanonLB f₁ d))
  obtain ⟨A₁, hA₁, hA₁c⟩ := cls_surj (r • cls M₁ hM₁ - r • cls K₁.bundle K₁.isLB -
    ∑ i, b i • cls (L₁ i) (h₁.isLB i))
  have hK : cls K.bundle K.isLB = CechPic.pull π (cls K₁.bundle K₁.isLB) :=
    _root_.GlobalTheory.cls_canonLB_baseChange R k R.subtype X₁ X f₁ f π d K₁ K hpb
  have hApull : cls (A₁.pull π) (pull_isLB hA₁ π) = cls A hA.isLB := by
    have e : cls A hA.isLB = r • cls M hM - r • cls K.bundle K.isLB - ∑ i, b i • cls (L i) (h.isLB i) := by
      rw [hcls]; abel
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, cls_pull hA₁, hA₁c, map_sub, map_sub, map_nsmul, map_nsmul, map_sum, ← hMc, ← hK]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, ← hL i]
  have hAamp : IsAmpleLB (A₁.pull π) :=
    IsAmpleLB.of_lbIso hA (pull_isLB hA₁ π) ((cls_eq_iff _ _).1 hApull)
  have hcls₁ : r • cls M₁ hM₁ = r • cls K₁.bundle K₁.isLB + ∑ i, b i • cls (L₁ i) (h₁.isLB i) +
      cls A₁ hA₁ := by
    rw [hA₁c]; abel
  have hv := GlobalTheory.T.kawamata_viehweg_spreading R k R.subtype X₁ X f₁ f π d hft Subtype.coe_injective hpb s L₁ σ₁ h₁ K₁
    M₁ A₁ hM₁ hA₁ r b hAamp hr hb hcls₁ q hq
  have hMM : cls (M₁.pull π) (pull_isLB hM₁ π) = cls M hM := by rw [cls_pull hM₁, hMc]
  exact _root_.GlobalTheory.Div.coh_subsingleton_of_cls_eq X (M₁.pull π) M _ hM hMM q hv

end GlobalTheory.Div
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealLogResolution
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem inMultAt_one_iff_kltAt {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] {p : X ⟶ Sp k} {n : ℕ} (hp : IsProjOver p)
    (hn : topologicalKrullDim X = n) {Δ : X → ℚ} {η : RatForms p n} {m : ℕ} {G : CartierDiv X}
    (hM : IsLogMult p n Δ η m G) (y : X) : InMultAt p n η m G y 1 ↔ KltAt p n Δ y := by
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hp
  have hkey : ∀ g, G.IsEqn y g → (KltAt p n Δ y ↔ ∀ (E : DivOver p), E.Through y → -1 < discrep E η m g) :=
    fun g hg => IsLogEqn.kltAt_iff hn hM.ne_zero hM.pos (hM.eqn y g hg)
  constructor
  · intro h
    obtain ⟨g, hg⟩ := G.exists_isEqn y
    rw [hkey g hg]
    intro E hE
    have h1 := h g hg E hE
    simpa [DivOver.ord_one] using h1
  · intro h g hg E hE
    have h1 := (hkey g hg).1 h E hE
    simpa [DivOver.ord_one] using h1

theorem one_mem_ideal_iff {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] {p : X ⟶ Sp k} {n : ℕ} (hp : IsProjOver p)
    (hn : topologicalKrullDim X = n) {Δ : X → ℚ} {η : RatForms p n} {m : ℕ} {G : CartierDiv X}
    (hM : IsLogMult p n Δ η m G) {J : X.IdealSheafData} (hJ : IsMultIdeal p n η m G J)
    (U : X.affineOpens) : (1 : Γ(X, U.1)) ∈ J.ideal U ↔ ∀ y ∈ U.1, KltAt p n Δ y := by
  rw [hJ U 1]
  constructor
  · intro h y hy
    exact (inMultAt_one_iff_kltAt hp hn hM y).1 (h y hy 1 (by simp))
  · intro h y hy u hu
    have : u = 1 := Units.ext (by simpa using hu)
    subst this
    exact (inMultAt_one_iff_kltAt hp hn hM y).2 (h y hy)

theorem mem_support_multIdeal_iff : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J → ∀ x : X, x ∈ J.support ↔ ¬ KltAt p n Δ x := by
  intro k _ _ X _ _ _ p n hp hn Δ η m G Y _ _ s _ K B hM hR J hJ x
  have hO := (isOpen_kltAt_and_lcAt_of_isLogRes k X p n hp hn Δ η m G Y s K B hM hR).1
  have hb : ∀ {U : X.Opens} {z : X}, z ∈ U → ∃ U' ∈ X.affineOpens, z ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
  constructor
  · intro hx hk
    obtain ⟨V, hV, hxV, hVO⟩ := hb (show x ∈ (⟨_, hO⟩ : X.Opens) from hk)
    have h1 : (1 : Γ(X, V)) ∈ J.ideal ⟨V, hV⟩ :=
      (one_mem_ideal_iff hp hn hM hJ ⟨V, hV⟩).2 (fun y hy => hVO hy)
    have h2 := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).1 hx
    rw [Scheme.mem_zeroLocus_iff] at h2
    exact h2 1 h1 (by rw [Scheme.basicOpen_one]; exact hxV)
  · intro hnk
    by_contra hx
    obtain ⟨V, hV, hxV, -⟩ := hb (show x ∈ (⊤ : X.Opens) from trivial)
    have h2 : ¬ x ∈ X.zeroLocus (J.ideal ⟨V, hV⟩ : Set Γ(X, V)) := fun h =>
      hx ((Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).2 h)
    rw [Scheme.mem_zeroLocus_iff] at h2
    push_neg at h2
    obtain ⟨f, hf, hfx⟩ := h2
    rw [Scheme.mem_basicOpen X f x hxV] at hfx
    haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
    have hgen : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ V x hxV f) =
        X.germToFunctionField V f := by simp
    have hunit : IsUnit (X.germToFunctionField V f) := by
      rw [← hgen]
      exact hfx.map _
    have hmem := (hJ ⟨V, hV⟩ f).1 hf x hxV hunit.unit (by rw [IsUnit.unit_spec]; rfl)
    apply hnk
    rw [← inMultAt_one_iff_kltAt hp hn hM x]
    intro g hg E hE
    have h3 := hmem g hg E hE
    have h4 : E.ord hunit.unit = 0 :=
      DivOver.ord_eq_zero_of_unitAt hE _ ⟨_, hfx, by rw [IsUnit.unit_spec]; exact hgen⟩
    simpa [h4, DivOver.ord_one] using h3

end GlobalTheory.Discrepancy
end

