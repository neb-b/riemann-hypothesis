module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1941
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0017
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2699

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResolutionDivisorsTopFormNormalCrossings
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ResPairSupp

theorem formOrd_ratPull_eq_zero {W Y : Scheme.{0}} [IsIntegral W] [IsIntegral Y]
    [IsLocallyNoetherian W] [IsLocallyNoetherian Y] (q : W ⟶ Sp ℂ) (n : ℕ)
    [SmoothOfRelativeDimension n q] (s : Y ⟶ W) [IsDominant s] [SmoothOfRelativeDimension n (s ≫ q)]
    (V : Y.Opens) (hV : Etale (V.ι ≫ s)) (ω : RatForms q n) (hω : ω ≠ 0) (K : CartierDiv W)
    (hK : IsDivOfForm K ω) (v : Y) (hv : v ∈ V) (hvK : s v ∉ K.supp) (F : DivOver (s ≫ q))
    (hF : F.IsAt v) : (fun ω => @dite ℤ (∃ a, F.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (ratPull q s n ω) = 0 := by
  obtain ⟨E, hE, -, hform⟩ := GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd Y W q s n V hV v hv F hF
  rw [hform ω hω, DivOver.formOrd_eq_mult_of_isDivOfForm ℂ W q n ω hω K hK E (s v) hE]
  have h1 : K.IsEqn (s v) 1 := not_not.1 hvK
  rw [h1.mult_eq, Units.val_one]
  exact (unitAt_one _).ord_eq_zero

theorem ord_fnPull_eq_zero {X W Y : Scheme.{0}} [IsIntegral X] [IsIntegral W] [IsIntegral Y]
    [IsLocallyNoetherian Y] (s₁ : W ⟶ X) [IsDominant s₁] (s₂ : Y ⟶ W) [IsDominant s₂]
    [IsDominant (s₂ ≫ s₁)] (G : CartierDiv X) (y v : Y) (g : X.functionFieldˣ) (hvy : v ⤳ y)
    (hv : s₂ v ∉ (pullCart s₁ G).supp) (hg : G.IsEqn ((s₂ ≫ s₁) y) g) :
    Scheme.ord (fnPull (s₂ ≫ s₁) g : Y.functionField) v = 0 := by
  rw [Scheme.Hom.comp_apply] at hg
  have h1 := isEqn_pullCart s₁ hg
  obtain ⟨U, hU, hUe⟩ := h1.exists_nhds
  have h2 := hUe (s₂ v) ((hvy.map s₂.continuous).mem_open U.isOpen hU)
  have h3 : UnitAt (s₂ v) ((fnPull s₁ g : W.functionField) / (1 : W.functionFieldˣ)) :=
    (not_not.1 hv).iff_unitAt.1 h2
  rw [Units.val_one, div_one] at h3
  have h4 := GlobalTheory.Cartier.PullDominant.unitAt_map s₂ h3
  have e : (fnPull (s₂ ≫ s₁) g : Y.functionField) = functionFieldMap s₂ (fnPull s₁ g) :=
    RingHom.congr_fun (functionFieldMap_comp_dominant s₁ s₂) g
  rw [e]
  exact h4.ord_eq_zero

end GlobalTheory.ResPairSupp

namespace GlobalTheory.ResPairSupp

theorem exists_resolution_supp : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n)
    (G D₀ : CartierDiv X), η ≠ 0 →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s)
      (B : Closeds Y),
      SmoothOfRelativeDimension n (s ≫ p) ∧ IsProper s ∧ Function.Bijective (functionFieldMap s) ∧
      {v : Y | v ∈ B ∧ Order.coheight v = 1}.Finite ∧ ratPull p s n η ≠ 0 ∧
      (∀ y : Y, ∃ (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y)
        (u : Fin n → Y.functionFieldˣ), IsSncChart (s ≫ p) n B y U hy z J w u) ∧
      (∀ (y v : Y) (g : X.functionFieldˣ), v ⤳ y → Order.coheight v = 1 → v ∉ B → G.IsEqn (s y) g →
        Scheme.ord (fnPull s g : Y.functionField) v = 0) ∧
      (∀ (y v : Y) (g : X.functionFieldˣ), v ⤳ y → Order.coheight v = 1 → v ∉ B → D₀.IsEqn (s y) g →
        Scheme.ord (fnPull s g : Y.functionField) v = 0) ∧
      (∀ (v : Y) (F : DivOver (s ≫ p)), Order.coheight v = 1 → v ∉ B → F.IsAt v →
        (fun ω => @dite ℤ (∃ a, F.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (ratPull p s n η) = 0) := by
  intro hP X _ _ p n hp hdim η G D₀ hη
  obtain ⟨W, s₁, U, hW, hsm₁, hpr₁, hU, hiso₁⟩ := GlobalTheory.WeakRes.weak_resolution hP ℂ X p n hp hdim
  haveI := hW
  haveI : IsDominant s₁ := isDominant_of_isIso_restrict X W s₁ U hU hiso₁
  have hbij₁ := functionFieldMap_bijective_of_isIso_restrict X W s₁ U hU hiso₁
  haveI := hsm₁
  haveI := SmoothOfRelativeDimension.smooth n (s₁ ≫ p)
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (s₁ ≫ p)
  have hη₁ : ratPull p s₁ n η ≠ 0 := fun h =>
    hη ((ratPull_bijective_of_birational ℂ X W p s₁ hbij₁ n).1 (h.trans (map_zero _).symm))
  obtain ⟨K₁, hK₁⟩ := (exists_isDivOfForm_and_toPic ℂ W (s₁ ≫ p) n _ hη₁).1
  let Z : Closeds W := (pullCart s₁ G).supp ⊔ (pullCart s₁ D₀).supp ⊔ K₁.supp
  have hZ : ∀ w, w ∉ Z → w ∉ (pullCart s₁ G).supp ∧ w ∉ (pullCart s₁ D₀).supp ∧ w ∉ K₁.supp :=
    fun w hw => ⟨fun h => hw (Or.inl (Or.inl h)), fun h => hw (Or.inl (Or.inr h)),
      fun h => hw (Or.inr h)⟩
  have hgZ : genericPoint W ∉ Z := by
    rintro ((h | h) | h)
    · exact (pullCart s₁ G).genericPoint_notMem_supp h
    · exact (pullCart s₁ D₀).genericPoint_notMem_supp h
    · exact K₁.genericPoint_notMem_supp h
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hIs : (I.support : Set W) = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have hI : I ≠ ⊥ := by
    intro h0
    have : genericPoint W ∈ (I.support : Set W) := by rw [h0]; simp
    rw [hIs] at this
    exact hgZ this
  obtain ⟨Y, s₂, hY, hsm, hpr, -, hiso₂, -, hsnc⟩ := hP ℂ n W (s₁ ≫ p) hW hsm₁ hpr₁ I hI
  haveI := hY
  haveI := hsm
  haveI := SmoothOfRelativeDimension.smooth n (s₂ ≫ s₁ ≫ p)
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (s₂ ≫ s₁ ≫ p)
  have hne : ((I.support.compl : W.Opens) : Set W).Nonempty := ⟨genericPoint W, by
    change genericPoint W ∉ (I.support : Set W)
    rw [hIs]; exact hgZ⟩
  haveI : IsDominant s₂ := isDominant_of_isIso_restrict W Y s₂ _ hne hiso₂
  have hbij₂ := functionFieldMap_bijective_of_isIso_restrict W Y s₂ _ hne hiso₂
  let B : Closeds Y := (I.comap s₂).support
  have hB : ∀ y, y ∈ B ↔ s₂ y ∈ Z := by
    intro y
    change y ∈ (B : Set Y) ↔ s₂ y ∈ (Z : Set W)
    rw [← hIs]
    simp only [B, Scheme.IdealSheafData.support_comap]
    rfl

  have hsm' : SmoothOfRelativeDimension n ((s₂ ≫ s₁) ≫ p) := by rw [Category.assoc]; exact hsm
  have hpr' : IsProjOver ((s₂ ≫ s₁) ≫ p) := by rw [Category.assoc]; exact hpr
  haveI := hsm'
  have hbij : Function.Bijective (functionFieldMap (s₂ ≫ s₁)) := by
    rw [functionFieldMap_comp_dominant s₁ s₂]
    exact hbij₂.comp hbij₁
  let V : Y.Opens := s₂ ⁻¹ᵁ I.support.compl
  have hV : Etale (V.ι ≫ s₂) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hVB : ∀ v, v ∉ B → v ∈ V := by
    intro v hv
    change s₂ v ∉ (I.support : Set W)
    rw [hIs]
    exact fun h => hv ((hB v).2 h)
  refine ⟨Y, hY, inferInstance, s₂ ≫ s₁, inferInstance, B, hsm', ?_, hbij, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have : IsProper ((s₂ ≫ s₁) ≫ p) := by
      obtain ⟨N, i, hi, hi'⟩ := hpr'
      have := isProper_str ℂ N
      rw [← hi']; infer_instance
    have : IsProper p := by
      obtain ⟨N, i, hi, rfl⟩ := hp
      have := isProper_str ℂ N
      infer_instance
    exact IsProper.of_comp (s₂ ≫ s₁) p
  · obtain ⟨r, w, D, σ, -, -, hw, -⟩ := GlobalTheory.T.exists_prime_divisors_snc_boundary ℂ Y ((s₂ ≫ s₁) ≫ p) n hpr' B hsnc
    refine (Set.finite_range w).subset ?_
    rintro v ⟨hvB, hv1⟩
    obtain ⟨i, rfl⟩ := hw v hv1 hvB
    exact ⟨i, rfl⟩
  · intro h
    exact hη ((ratPull_bijective_of_birational ℂ X Y p (s₂ ≫ s₁) hbij n).1
      (h.trans (map_zero _).symm))
  · intro y
    exact GlobalTheory.T.exists_snc_chart ℂ Y ((s₂ ≫ s₁) ≫ p) n B hsnc y
  · intro y v g hvy _ hvB hg
    exact ord_fnPull_eq_zero s₁ s₂ G y v g hvy (fun h => hvB ((hB v).2 (Or.inl (Or.inl h)))) hg
  · intro y v g hvy _ hvB hg
    exact ord_fnPull_eq_zero s₁ s₂ D₀ y v g hvy (fun h => hvB ((hB v).2 (Or.inl (Or.inr h)))) hg
  · intro v F _ hvB hF
    have hvK : s₂ v ∉ K₁.supp := fun h => hvB ((hB v).2 (Or.inr h))
    have key : ∀ (q : Y ⟶ Sp ℂ) (e : s₂ ≫ s₁ ≫ p = q) (F : DivOver q) (_ : F.IsAt v)
        (h : (functionFieldMap (s₂ ≫ s₁)).comp (Cartier.constFn p) = Cartier.constFn q),
        F.formOrd (TopForm.formMap n (functionFieldMap (s₂ ≫ s₁)) h η) = 0 := by
      intro q e
      subst e
      intro F hF h
      have e2 : ratPull (s₁ ≫ p) s₂ n (ratPull p s₁ n η) =
          TopForm.formMap n (functionFieldMap (s₂ ≫ s₁)) h η :=
        formMap_formMap _ _ _ (functionFieldMap_comp_dominant s₁ s₂).symm _ _ _ η
      rw [← e2]
      exact formOrd_ratPull_eq_zero (s₁ ≫ p) n s₂ V hV _ hη₁ K₁ hK₁ v (hVB v hvB) hvK F hF
    exact key _ (Category.assoc s₂ s₁ p).symm F hF _

end GlobalTheory.ResPairSupp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometric
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke.TateTransl

section Ev

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {κ : Type} [Field κ] {Q : Type} [Group Q] {act : D.O → Q → Q}
  {e : ℕ → Q → Q → κˣ → Prop} (I : TateIsoO D κ Q act e)

theorem ev_zero (n : ℕ) : I.ev n 0 = 1 := by
  have h := I.add n 0 0
  rw [add_zero] at h
  simpa using h

theorem ev_nsmul (n j : ℕ) (w : D.La) : I.ev n (j • w) = I.ev n w ^ j := by
  induction j with
  | zero => rw [zero_smul, ev_zero, pow_zero]
  | succ j ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem ev_neg (n : ℕ) (w : D.La) : I.ev n (-w) = (I.ev n w)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← I.add, neg_add_cancel, ev_zero])

theorem ev_eq_iff (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (w w' : D.La) :
    I.ev n w = I.ev n w' ↔ ∃ y, w - w' = n • y := by
  rw [← I.ker n hn hnp, sub_eq_add_neg, I.add, ev_neg, mul_inv_eq_one]

theorem ev_mul_nsmul (n j : ℕ) (hn : 0 < n) (hj : 0 < j) (hc : (j * n).Coprime p) (w : D.La) :
    I.ev (n * j) (n • w) = I.ev j w := by
  rw [ev_nsmul, mul_comm n j, I.tower j n hj hn hc]

end Ev

theorem one_comp_transl_pt {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (h : 𝟙_ (Over S) ⟶ A) :
    (1 : T ⟶ A) ≫ transl h = toUnit T ≫ h := by
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique ((1 : T ⟶ A) ≫ toUnit A) (toUnit T),
    _root_.one_mul]

theorem exists_tateIsoO_transl : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ A') (fun c g => g ≫ act'.act c) (fun n g g' z => Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta (g y) ≫ ψ) = I.ev N y := by
  intro p _ D R _ b g c k N hcp hkp hN hNp hEF hg hck S s o A' _ _ act' ψ hA' hψ hGal hact P' hP' r₁ r₂ hiso κ _ _ x β hx
  obtain ⟨I, hI⟩ := o.geom κ x β hx
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have kpos : 0 < k := Nat.pos_of_ne_zero fun h => by subst h; rw [Nat.coprime_zero_left] at hkp; omega
  have cpos : 0 < c := Nat.pos_of_ne_zero fun h => by subst h; rw [Nat.coprime_zero_left] at hcp; omega
  have Npos : 0 < N := by omega
  haveI := D.freeLa
  let Ψ : (Over.mk x ⟶ o.A) →* (Over.mk x ⟶ A') :=
    MonoidHom.mk' (fun t => t ≫ ψ) (fun a a' => MonObj.mul_comp a a' ψ)
  have hΨ : ∀ t, Ψ t = t ≫ ψ := fun _ => rfl
  have ginj : Function.Injective g := by
    intro u v huv
    have h0 : D.EF (u - v) = 0 := by
      ext w
      have e := hEF (u - v) w
      rw [map_sub, huv, sub_self, map_zero, LinearMap.zero_apply] at e
      rw [LinearMap.zero_apply]
      exact (mul_eq_zero.1 e.symm).resolve_left (by exact_mod_cast cpos.ne')
    have := D.nondeg (h0.trans (map_zero D.EF).symm)
    exact sub_eq_zero.1 this
  have hlev : ∀ n, 0 < n → n.Coprime p → ∀ w, I.ev (n * k) (n • w) = I.ev k w := fun n hn hnp w =>
    ev_mul_nsmul I n k hn kpos (Nat.Coprime.mul_left hkp hnp) w
  have hker : ∀ t : Over.mk x ⟶ o.A, t ≫ ψ = 1 ↔ ∃ z, t = I.ev (N * k) (N • g z) := by
    intro t
    constructor
    · intro ht
      have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
        rw [← Over.comp_left, ← Over.comp_left, ht, MonObj.one_comp]
      obtain ⟨h, hh, -⟩ := hGal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
      obtain ⟨z, hz⟩ := h.2
      refine ⟨z, ?_⟩
      have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl h.1 := Over.OverMorphism.ext (by rw [Over.comp_left]; exact hh.symm)
      rw [e2, one_comp_transl_pt, hz, hI]
    · rintro ⟨z, rfl⟩
      rw [← hI, Category.assoc, comp_eq_one_of_transl ψ (o.eta (N • g z)) (hGal.inv ⟨_, mem_heckeSub o g N z⟩),
        MonObj.comp_one]
  have ker' : ∀ n, 0 < n → n.Coprime p → ∀ y, I.ev (n * k) (g y) ≫ ψ = 1 ↔ ∃ z, y = n • z := by
    intro n hn hnp y
    rw [hker]
    constructor
    · rintro ⟨z, hz⟩
      rw [hlev N Npos hNp, ← hlev n hn hnp] at hz
      obtain ⟨w, hw⟩ := (ev_eq_iff I (n * k) (Nat.mul_pos hn kpos) (Nat.Coprime.mul_left hnp hkp) _ _).1 hz
      obtain ⟨w', hw'⟩ := hg w
      refine ⟨z + w', ginj ?_⟩
      rw [map_nsmul, map_add (f := _), hw', smul_add, smul_smul, ← sub_eq_iff_eq_add', hw]
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [map_nsmul, hlev n hn hnp, hlev N Npos hNp]⟩

  have htor : ∀ n, 0 < n → n.Coprime p → ∀ y, (I.ev (n * k) (g y) ≫ ψ) ^ n = 1 := by
    intro n hn hnp y
    rw [← hΨ, ← map_pow, hΨ, ← ev_nsmul, ← map_nsmul]
    exact (ker' n hn hnp (n • y)).2 ⟨y, rfl⟩
  have onto' : ∀ n, 0 < n → n.Coprime p → ∀ q : Over.mk x ⟶ A', q ^ n = 1 ↔ ∃ y, I.ev (n * k) (g y) ≫ ψ = q := by
    intro n hn hnp q
    constructor
    · intro hq
      haveI := hGal.fin
      haveI := hGal.onto
      obtain ⟨a₀, ha₀⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left q.left
      let a : Over.mk x ⟶ o.A := Over.homMk a₀ (by
        show a₀ ≫ o.A.hom = x
        rw [← Over.w ψ, ← Category.assoc, ← ha₀, Over.w q]; rfl)
      have ha : a ≫ ψ = q := Over.OverMorphism.ext (by rw [Over.comp_left]; exact ha₀.symm)
      have han : (a ^ n) ≫ ψ = 1 := by rw [← hΨ, map_pow, hΨ, ha, hq]
      obtain ⟨z, hz⟩ := (hker _).1 han
      rw [hlev N Npos hNp, ← hlev n hn hnp] at hz
      have hnk : 0 < n * k := Nat.mul_pos hn kpos
      have hnkp : (n * k).Coprime p := Nat.Coprime.mul_left hnp hkp
      have hak : a ^ (n * k) = 1 := by
        rw [pow_mul, hz, ← ev_nsmul, I.ker _ hnk hnkp]
        exact ⟨g z, by rw [smul_smul, mul_comm]⟩
      obtain ⟨w, hw⟩ := (I.onto _ hnk hnkp a).1 hak
      rw [← hw, ← ev_nsmul, ev_eq_iff I _ hnk hnkp] at hz
      obtain ⟨v, hv⟩ := hz
      have e1 : n • (w - g z - k • v) = 0 := by rw [smul_sub, smul_sub, smul_smul, ← hv, sub_self]
      have e2 : w - g z - k • v = 0 := by
        have e3 : ((n : ℤ)) • (w - g z - k • v) = 0 := by rw [natCast_zsmul]; exact e1
        exact (smul_eq_zero.1 e3).resolve_left (by exact_mod_cast hn.ne')
      have e4 : w = g z + k • v := by rw [sub_sub, sub_eq_zero] at e2; exact e2
      obtain ⟨v', hv'⟩ := hg v
      refine ⟨z + v', ?_⟩
      rw [map_add (f := _), hv', ← e4, hw, ha]
    · rintro ⟨y, rfl⟩
      exact htor n hn hnp y

  have hnκ : ∀ n : ℕ, n.Coprime p → (n : κ) ≠ 0 := fun n hnp => by
    have h := (b.unit n hnp).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have hiso2 : LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (k ^ 2 / c))
      ((P'.pull (lift (𝟙 A') (𝟙 A')).left).pull ψ.left) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb (pull_isLB o.isLB _) _ _) (pull_isLB (pull_isLB hP' _) _)).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow (pull_isLB o.isLB _), GlobalTheory.CechPic.cls_pull o.isLB, GlobalTheory.CechPic.cls_pull (pull_isLB hP' _),
      GlobalTheory.CechPic.cls_pull hP', ← GlobalTheory.CechPic.pull_comp]
    have h1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o.isLB _ _) (pull_isLB hP' _)).2 hiso
    rw [GlobalTheory.CechPic.cls_linComb o.isLB, GlobalTheory.CechPic.cls_pull hP'] at h1
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift (𝟙 o.A) (𝟙 o.A)).left) h1
    rw [map_nsmul, ← GlobalTheory.CechPic.pull_comp] at h2
    rw [h2]
    congr 1
    simp only [sq2, ← Over.comp_left, comp_lift, Category.id_comp, lift_fst_assoc, lift_snd_assoc, Category.comp_id]
  refine ⟨⟨I.ζ, I.ζ_prim, I.ζ_pow, fun n y => I.ev (n * k) (g y) ≫ ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun y => ?_⟩
  · intro n y y'
    rw [map_add (f := _), I.add, MonObj.mul_comp]
  · intro n b' y
    rw [map_smul, I.lin, Category.assoc, hact, ← Category.assoc]
  · exact fun n hn hnp y => ker' n hn hnp y
  · exact fun n hn hnp q => onto' n hn hnp q
  · intro n m hn hm hnm y
    rw [← hΨ, ← map_pow, hΨ, Nat.mul_right_comm n m k, I.tower (n * k) m (Nat.mul_pos hn kpos) hm
      (by rw [Nat.mul_right_comm]; exact Nat.Coprime.mul_left hnm hkp)]
  · intro n hn hnp u v
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_weilCommutatorPairing_torsion_geometricPoint S A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) hA' (pull_isLB hP' _) κ x n hn (hnκ n hnp) _ _
      (htor n hn hnp u) (htor n hn hnp v)
    have h2 := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds o.ab (pull_isLB o.isLB _) (pull_isLB hP' _) ψ hiso2 he
    have h3 := _root_.GlobalTheory.UPel.HT.Hecke.weil_value_translate p D R b g c k (N * k) hcp hkp hEF hg hck S s o κ x β hx I n hn hnp u v e
      (by rw [Nat.cast_mul]; exact h2)
    rw [h3] at he
    exact he
  · show toUnit _ ≫ (o.eta (g y) ≫ ψ) = I.ev (N * k) (g y) ≫ ψ
    rw [← Category.assoc, hI]

end GlobalTheory.UPel.HT.Hecke.TateTransl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermsMumfordFormalSectionTranslates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam

theorem exists_secT_weight_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (N : ℕ) (σ₀ : LB.Sec (LB.LinComb D.P.L (K := Fin 2) ![𝟙 D.P.A.left, a.left] ![(N : ℤ), -1])) (β : D.X), β = 0 → ∃ s : SecT D a N (-1) β, ∀ (Z : Scheme.{0}) (x : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J → sval s x z J = sval σ₀ x z J := by
  intro R _ _ D a N σ₀ β hβ
  subst hβ
  have hc : (toUnit D.P.A ≫ D.c 0) = (1 : D.P.A ⟶ D.P.A) := GlobalTheory.CoordToExt.c_zero D D.P.A
  have h1 : (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = 𝟙 D.P.A.left := by
    rw [hc]
    have e : padd D.P.A (𝟙 D.P.A) (1 : D.P.A ⟶ D.P.A) = 𝟙 D.P.A * 1 := rfl
    rw [e, _root_.mul_one]
    rfl
  have h2 : (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left := by
    rw [hc]
    rfl
  obtain ⟨d, hd⟩ := GlobalTheory.exists_sec_relation_defect D.P.A.left D.P.A.left D.P.A.left D.P.L D.P.isLB _ _ _
    ![𝟙 D.P.A.left, a.left] ![(N : ℤ), -1] (tφ D a 0) (tε N (-1)) _ _ (𝟙 _) σ₀
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.secZero _) (LB.oneGen D.P.L) (-1) 0 GlobalTheory.CoordToExt.isGen_one
    (fun U _ f => by
      simp only [tφ, tε, h1, h2, Fin.prod_univ_five, Fin.prod_univ_two, Fintype.prod_sum_type,
        Sum.elim_inl, Sum.elim_inr, Category.id_comp, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]
      simp
      group)
  refine ⟨d, fun Z x z J hJ => ?_⟩
  have k0 : gs x z ⊤ (0 : Γ(D.P.A.left, ⊤)) = 0 := by
    rw [gs_eq x z ⊤ (by simp)]
    first
      | (rw [map_zero, map_zero]; done)
      | simp [map_zero]
  have k1 : gs x z ⊤ (-1 : Γ(D.P.A.left, ⊤)) = -1 := by
    rw [gs_eq x z ⊤ (by simp)]
    first
      | (rw [map_neg, map_one, map_neg, map_one]; done)
      | simp [map_neg, map_one]
  rw [hd Z x z J hJ, val_one, k0, k1, Category.comp_id]
  simp

theorem exists_terms : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])), ∃ (s₀ : SecT D.toPre a N (-1) 0) (s : ∀ ν, SecT D.toPre a N (-1) (shift h h' N (-1) ν)), (∀ ν, TRel h ν s₀ (s ν)) ∧ Small (maximalIdeal R) s ∧ (∀ ν, ν ≠ 0 → Van (maximalIdeal R) (s ν) 0) ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (s 0) x z J = sval σ₀ x z J) := by
  intro R _ _ _ hB D a a' h h' hE N hN hP σ₀
  obtain ⟨r, g, hg, hr, hfin, hval⟩ := GlobalTheory.MumInt.main R hB D a a' h h' hE N hN hP
  obtain ⟨s₀, hs₀⟩ := exists_secT_weight_zero R D.toPre a N σ₀ 0 rfl
  have h0 : shift h h' (N : ℤ) (-1) (0 : D.toPre.X) = 0 := by simp [shift]
  obtain ⟨z₀, hz₀⟩ := exists_secT_weight_zero R D.toPre a N σ₀ _ h0
  have key : ∀ ν, ∃ t : SecT D.toPre a N (-1) (shift h h' N (-1) ν), TRel h ν s₀ t ∧
      ∀ e : ℕ, r ν ∈ maximalIdeal R ^ (e + 1) → Van (maximalIdeal R) t e := by
    intro ν
    obtain ⟨u₀, hu₀, hfac⟩ := GlobalTheory.T.exists_normalised_twistedGenerator_of_factor R hB D a a' h h' hE N hN r g hg hval ν
    exact GlobalTheory.T.exists_mumfordTerm_translate_normalisedGenerator R D a h h' N s₀ ν u₀ hu₀ (r ν) hfac
  choose t ht using key
  have hz : TRel h 0 s₀ z₀ :=
    _root_.GlobalTheory.TwFac.trel_zero R hB D a a' h h' hE N hN s₀ z₀ fun Z x z J hJ => (hz₀ Z x z J hJ).trans (hs₀ Z x z J hJ).symm
  classical
  let s : ∀ ν, SecT D.toPre a N (-1) (shift h h' N (-1) ν) := fun ν =>
    if hν : ν = 0 then hν.symm ▸ z₀ else t ν
  have hs0 : s 0 = z₀ := dif_pos rfl
  have hsν : ∀ ν, ν ≠ 0 → s ν = t ν := fun ν hν => dif_neg hν
  refine ⟨s₀, s, fun ν => ?_, fun e => ?_, fun ν hν => ?_, fun Z x z J hJ => ?_⟩
  · by_cases hν : ν = 0
    · subst hν
      rw [hs0]
      exact hz
    · rw [hsν ν hν]
      exact (ht ν).1
  · refine ((hfin (e + 1)).insert 0).subset fun ν hν => ?_
    by_cases h0' : ν = 0
    · exact Or.inl h0'
    · refine Or.inr fun hm => hν ?_
      rw [hsν ν h0']
      exact (ht ν).2 e hm
  · rw [hsν ν hν]
    exact (ht ν).2 0 (by rw [zero_add, pow_one]; exact hr ν hν)
  · rw [hs0]
    exact hz₀ Z x z J hJ

end GlobalTheory.TwFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendFiniteModif
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem extend_finiteModif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (I : Type) [Finite I] (k : I → ℕ) (s : ∀ i, SecK L α (k i)), (∀ i, TraitReg M G L (s i)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h ∧ M'.gp ≫ h = M.gp ∧ h ≫ M.π = M'.π ∧ ∀ i, ∃ σ : SecK L (pullback.fst G.hom h) (k i), Agree L σ (s i) := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb I _ k s hs
  exact _root_.GlobalTheory.Mum.extend_locInt R M G hsm hqc hgi L hL Y α t hpb I k s
    (fun i => _root_.GlobalTheory.Mum.locInt_of_traitReg R M G hsm hqc hgi L hL Y α t hpb (k i) (s i) (hs i))

end GlobalTheory.Mum
end
end

