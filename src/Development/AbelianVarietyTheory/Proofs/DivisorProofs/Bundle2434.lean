module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionTransportPullbackIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum

theorem exists_secK_of_iso_pull : ∀ {X X' : Scheme.{0}} (L : LB X) (L' : LB X') (f : X' ⟶ X) (w : LB.Iso L' (L.pull f)), L.IsLB → L'.IsLB → w.IsGen → ∀ (N : ℕ) (t : H0 L' N), ∃ s : SecK L f N, ∀ (Z : Scheme.{0}) (p : Z ⟶ X') (z : Z) J J', Good L z J → Good L' z J' → sval s p z J = (gw w p z (J (p ≫ f)) (J' p) ^ N).val * sval t p z J' := by
  intro X X' L L' f w hL hL' hw N t
  have hp := (isGen_iff w).1 hw
  have mL : ∀ (j : Fin 1 → L.ι) (x : X'), x ∈ LB.wchart L (fun _ : Fin 1 => f) j → f x ∈ L.U (j 0) :=
    fun j x hx => Set.mem_iInter.1 hx 0
  have mL' : ∀ (k : L'.ι) (x : X'), x ∈ L'.U k → x ∈ LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k) :=
    fun k x hx => Set.mem_iInter.2 fun _ => hx
  have indep : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k k' : L'.ι), f (r z) ∈ L.U j → r z ∈ L'.U k →
      r z ∈ L'.U k' →
      (gw w r z j k ^ N).val * gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (t.f (fun _ => k)) =
      (gw w r z j k' ^ N).val * gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k')) (t.f (fun _ => k')) := by
    intro Z r z j k k' hj hk hk'
    rw [sec_trans t r z (mL' k _ hk) (mL' k' _ hk'), hp Z r z j j k k' hj hj hk hk', gm_self hL (r ≫ f) z hj,
      ← _root_.mul_assoc, ← Units.val_mul, trF, Fin.prod_univ_one, Category.comp_id, zpow_natCast, ← mul_pow, _root_.one_mul,
      mul_right_comm, inv_mul_cancel, _root_.one_mul]
  have glue : ∀ j : Fin 1 → L.ι, ∃ a : Γ(X', LB.wchart L (fun _ : Fin 1 => f) j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (k : L'.ι), r z ∈ LB.wchart L (fun _ : Fin 1 => f) j → r z ∈ L'.U k →
      gs r z _ a = (gw w r z (j 0) k ^ N).val *
        gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (t.f (fun _ => k)) := by
    intro j
    let W : L'.ι → X'.Opens := fun k => LB.wchart L (fun _ : Fin 1 => f) j ⊓ L'.U k
    have l₁ : ∀ k, W k ≤ (L.pull f).U (fun _ => j 0) ⊓ L'.U k := fun k x hx => ⟨mem_pull.2 (mL j x hx.1), hx.2⟩
    have l₂ : ∀ k, W k ≤ LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k) := fun k x hx => mL' k x hx.2
    obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(X', W k), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) k, r z ∈ W k →
        gs r z (W k) (u k) = (gw w r z (j 0) k ^ N).val *
          gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (t.f (fun _ => k)) :=
      ⟨fun k => (res (l₁ k) (w.s (fun _ => j 0, k)) ^ N).val *
          (X'.presheaf.map (homOfLE (l₂ k)).op).hom (t.f (fun _ => k)), fun Z r z k hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans
          (congrArg Units.val ((map_pow _ _ _).trans (congrArg (· ^ N) (gm_res r z (l₁ k) hz _)))))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' W (LB.wchart L (fun _ : Fin 1 => f) j)
      (fun k => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL' y
        exact Opens.mem_iSup.2 ⟨k, hy, hk⟩) u
      (fun k k' => fn_ext (V := W k ⊓ W k') fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        rw [hu _ _ y k hy.1, hu _ _ y k' hy.2]
        exact indep _ (𝟙 X') y (j 0) k k' (mL j y hy.1.1) hy.1.2 hy.2.2)
    refine ⟨a, fun Z r z k h₁ h₂ => ?_⟩
    have hz : r z ∈ W k := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W k)) (ha k)).trans (hu Z r z k hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J J' hJ hJ' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL' y
    refine (gs_res (𝟙 X') y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 X') y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 X') y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 X') y j j' hy.1 hy.2)))
      (gs_res (𝟙 X') y _ hy _))).symm)
    refine (ha j _ (𝟙 X') y k hy.1 hk).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 X') y k hy.2 hk)).symm)
    rw [hp _ (𝟙 X') y (j 0) (j' 0) k k (mL j y hy.1) (mL j' y hy.2) hk hk, gm_self hL' (𝟙 X') y hk, inv_one, _root_.mul_one,
      mul_pow, Units.val_mul, _root_.mul_assoc, Fin.prod_univ_one, zpow_natCast]
  · rw [sval_of t r z J' (fun _ => J' r) (fun _ => by rw [Category.comp_id])]
    exact ha _ Z r z (J' r) (hJ.mem (fun _ : Fin 1 => f) r) (hJ' r)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationProd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.ProdLin

theorem exists_linearisation_prod : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ga Gb : Type) [Group Ga] [Group Gb] (ρ₁ : Ga → (X ⟶ X)) (ρ₂ : Gb → (X ⟶ X)) (ρ : Ga × Gb → (X ⟶ X)), (∀ p, ρ p = ρ₁ p.1 ≫ ρ₂ p.2) → (∀ a b, ρ₁ a ≫ ρ₂ b = ρ₂ b ≫ ρ₁ a) → (∀ a c, ρ₁ (a * c) = ρ₁ a ≫ ρ₁ c) → (∀ b d, ρ₂ (b * d) = ρ₂ b ≫ ρ₂ d) → ∀ (v₁ : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₁ a] ![1, -1])) (v₂ : ∀ b, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₂ b] ![1, -1])), (∀ a, (v₁ a).IsGen) → (∀ b, (v₂ b).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (v₁ (a * c)) (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₁ c) (ρ₁ a)))) → (∀ b d, LB.Gen.Corr L _ _ _ _ (v₂ (b * d)) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₂ d) (ρ₂ b)))) → (∀ a b, LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₂ b) (ρ₁ a))) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₁ a) (ρ₂ b)))) → ∃ u : ∀ p : Ga × Gb, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ p] ![1, -1]), (∀ p, (u p).IsGen) ∧ ∀ p q, LB.Gen.Corr L _ _ _ _ (u (p * q)) (LB.mulGen L _ _ _ _ (u p) (LB.pullGen L _ _ (u q) (ρ p))) := by
  intro X L hL Ga Gb _ _ ρ₁ ρ₂ ρ hρ hcomm hρ₁ hρ₂ v₁ v₂ hv₁ hv₂ hc₁ hc₂ hc
  have hex : ∀ p : Ga × Gb, ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ p] ![1, -1]), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
        val u r z J = val (LB.mulGen L _ _ _ _ (v₁ p.1) (LB.pullGen L _ _ (v₂ p.2) (ρ₁ p.1))) r z J := by
    intro p
    refine exists_gen hL ?_ _ (DVR.mulGen_isGen_of_isGen _ (hv₁ _) _ (DVR.pullGen_isGen_of_isGen _ _ _ (hv₂ _) _))
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_two, hρ p]
  choose u hu hval using hex
  refine ⟨u, hu, fun p q => ?_⟩
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  refine corr_of_val hL fun y J hJ => ?_
  have e0 := hval (a * c, b * d) X (𝟙 X) y J hJ
  have e1 := hval (a, b) X (𝟙 X) y J hJ
  have e2 := hval (c, d) X (𝟙 X ≫ ρ (a, b)) y J hJ
  have f1 := val_corr hJ (hc₁ a c) (𝟙 X)
  have f2 := val_corr hJ (hc₂ b d) (ρ₁ (a * c))
  have g := val_corr hJ (hc c b) (ρ₁ a)
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at e0
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at e1
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at e2
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at f1
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at f2
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at g
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁]
  rw [e0, e1, e2, f1, f2, ← hcomm c b, _root_.mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (val (v₁ c) (ρ₁ a) y J), g]
  simp only [_root_.mul_assoc]
end GlobalTheory.ProdLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCanonicalMultipleOfGloballyKlt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KltGlobal

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {n : ℕ}
  {Δ : X → ℚ} {η : RatForms p n} {x y : X} {m : ℕ} {g h : X.functionFieldˣ}

theorem compactSpace_of_isProjOver' {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Sp R}
    (hf : IsProjOver f) : CompactSpace Y := by
  obtain ⟨N, i, hi, rfl⟩ := hf
  have := isProper_str R N
  have : IsProper (i ≫ PSpace.str R N) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R N)

theorem unitAt_of_specializes' {z : X} {f : X.functionField} (hz : z ⤳ y) (hf : UnitAt y f) :
    UnitAt z f :=
  (unitAt_iff hf.ne_zero).2 ⟨regAt_of_specializes hz hf.regAt, regAt_of_specializes hz hf.inv.regAt⟩

theorem ord_eq_zero_of_unitAt' {E : DivOver p} {z : X} (hE : E.IsAt z) {u : X.functionFieldˣ}
    (hu : UnitAt z (u : X.functionField)) : E.ord u = 0 := by
  have h1 := (E.ord_nonneg_iff u).2 ((hE _).2 hu.regAt)
  have h2 := (E.ord_nonneg_iff u⁻¹).2 ((hE _).2 (by rw [Units.val_inv_eq_inv_val]; exact hu.inv.regAt))
  rw [E.ord_inv] at h2
  omega

theorem isLogEqn_pow' (hg : IsLogEqn p Δ η x m g) (r : ℕ) : IsLogEqn p Δ η x (m * r) (g ^ r) := by
  intro z hz E hE
  rw [E.ord_pow]
  push_cast
  rw [← hg z hz E hE]
  ring

theorem isLogEqn_of_unitAt' (hg : IsLogEqn p Δ η y m g)
    (hu : UnitAt y ((h : X.functionField) / g)) : IsLogEqn p Δ η y m h := by
  intro z hz E hE
  have h0 : E.ord (h * g⁻¹) = 0 := ord_eq_zero_of_unitAt' hE (by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
    exact unitAt_of_specializes' hz hu)
  have e : E.ord h = E.ord g := by
    have := E.ord_mul (h * g⁻¹) g
    rwa [inv_mul_cancel_right, h0, zero_add] at this
  rw [hg z hz E hE, e]

theorem unitAt_of_isLogEqn' [LocallyOfFiniteType p] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (hg : IsLogEqn p Δ η y m g) (hh : IsLogEqn p Δ η y m h) :
    UnitAt y ((h : X.functionField) / g) := by
  have h0 : ∀ z, z ⤳ y → ∀ F : DivOver p, F.IsAt z → F.ord (h * g⁻¹) = 0 := by
    intro z hz F hF
    have a := hg z hz F hF
    have b := hh z hz F hF
    rw [F.ord_mul, F.ord_inv]
    have : (F.ord g : ℚ) = F.ord h := a.symm.trans b
    have : F.ord g = F.ord h := by exact_mod_cast this
    omega
  have reg : ∀ v : X.functionFieldˣ, (∀ z, z ⤳ y → ∀ F : DivOver p, F.IsAt z → F.ord v = 0) →
      RegAt y (v : X.functionField) := fun v hv =>
    regAt_of_forall_coheight_eq_one fun z hz h1 =>
      have ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) h1
      (hF _).1 ((F.ord_nonneg_iff v).1 (hv z hz F hF).ge)
  have hne : (h : X.functionField) / g ≠ 0 := div_ne_zero h.ne_zero g.ne_zero
  have e1 : ((h * g⁻¹ : X.functionFieldˣ) : X.functionField) = h / g := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  have e2 : (((h * g⁻¹)⁻¹ : X.functionFieldˣ) : X.functionField) = ((h : X.functionField) / g)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, e1]
  refine (unitAt_iff hne).2 ⟨e1 ▸ reg _ h0, e2 ▸ reg _ fun z hz F hF => ?_⟩
  rw [F.ord_inv, h0 z hz F hF, neg_zero]

theorem exists_isLogEqn_of_form' [PerfectField k] [LocallyOfFiniteType p]
    (hn : topologicalKrullDim X = n) {η₀ : RatForms p n} (hη₀ : η₀ ≠ 0) (hη : η ≠ 0)
    (hg : IsLogEqn p Δ η x m g) : ∃ g' : X.functionFieldˣ, IsLogEqn p Δ η₀ x m g' := by
  by_cases hE : Nonempty (DivOver p)
  · obtain ⟨E⟩ := hE
    obtain ⟨ω, hω, f₀, e₀, -⟩ := E.isFormOrd_formOrd hn hη₀
    obtain ⟨f, e⟩ := (E.isFreeGen_toRat hω).2 η
    have hf : f ≠ 0 := fun h0 => hη (by rw [← e, h0]; exact zero_smul _ _)
    obtain ⟨c, hc⟩ : ∃ c : X.functionFieldˣ, η = (c : X.functionField) • η₀ :=
      ⟨Units.mk0 f hf * f₀⁻¹, by rw [e₀, smul_smul, ← e]; simp⟩
    refine ⟨g * (c ^ m)⁻¹, fun z hz F hF => ?_⟩
    have a := hg z hz F hF
    rw [hc, F.formOrd_smul hn hη₀] at a
    rw [F.ord_mul, F.ord_inv, F.ord_pow]
    push_cast at a ⊢
    linear_combination a
  · exact ⟨1, fun z _ F _ => (hE ⟨F⟩).elim⟩

theorem exists_nhds_isLogEqn' [IsLocallyNoetherian X] [CompactSpace X]
    (hfin : {z : X | ∃ E : DivOver p, E.IsAt z ∧ (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η ≠ 0}.Finite)
    (hΔ : (Function.support Δ).Finite) (hg : IsLogEqn p Δ η x m g) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, IsLogEqn p Δ η y m g := by
  set B : Set X := {z | ∃ E : DivOver p, E.IsAt z ∧ (m : ℚ) * (E.formOrd η + Δ z) ≠ E.ord g}
    with hB
  have hBf : B.Finite := by
    refine ((hfin.union hΔ).union (CartierDiv.principal g).finite_support_mult).subset ?_
    rintro z ⟨E, hE, hne⟩
    by_cases h1 : E.formOrd η = 0
    · by_cases h2 : Δ z = 0
      · right
        show (CartierDiv.principal g).mult z ≠ 0
        rw [(CartierDiv.isEqn_principal g z).mult_eq, ← hE.ord_eq]
        intro h3
        apply hne
        rw [h1, h2, h3]
        simp
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl ⟨E, hE, h1⟩)
  have key : ∀ y, y ∈ closure B → ∃ z ∈ B, z ⤳ y := by
    intro y hy
    have hc : closure B = ⋃ z ∈ B, closure {z} := by
      conv_lhs => rw [← Set.biUnion_of_singleton B]
      exact hBf.closure_biUnion _
    rw [hc] at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨z, hz, hy⟩ := hy
    exact ⟨z, hz, specializes_iff_mem_closure.2 hy⟩
  refine ⟨⟨(closure B)ᶜ, isClosed_closure.isOpen_compl⟩, show x ∉ closure B from fun hx => ?_,
    fun y hy z hz E hE => ?_⟩
  · obtain ⟨z, ⟨E, hE, hne⟩, hzx⟩ := key x hx
    exact hne (hg z hzx E hE)
  · have hy' : y ∉ closure B := hy
    by_contra hne
    exact hy' (closure_mono (Set.singleton_subset_iff.2 (show z ∈ B from ⟨E, hE, hne⟩))
      (specializes_iff_mem_closure.1 hz))

end GlobalTheory.KltGlobal

namespace GlobalTheory.Discrepancy

open GlobalTheory.KltGlobal

theorem exists_isLogCanonicalMultiple_of_kltAt :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
      (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p →
      topologicalKrullDim X = n → ∀ Δ : X → ℚ, IsEffQDiv Δ → (∀ y, KltAt p n Δ y) →
      ∃ (m : ℕ) (G : CartierDiv X), 0 < m ∧ IsLogCanonicalMultiple p n Δ m G := by
  intro X _ _ _ p n hP hn Δ hΔ hklt
  classical
  haveI : CompactSpace X := compactSpace_of_isProjOver' hP
  haveI : LocallyOfFiniteType p := isProjOver_locallyOfFiniteType ℂ X p hP
  obtain ⟨η₀, -, -, hη₀, -, -, -⟩ := hklt (genericPoint X)
  have hfin := GlobalTheory.FormOrdFinite.finite_setOf_formOrd_ne_zero ℂ X p n hP hn η₀ hη₀
  have h1 : ∀ x, ∃ (m : ℕ) (g : X.functionFieldˣ) (U : X.Opens), 0 < m ∧ x ∈ U ∧
      ∀ y ∈ U, IsLogEqn p Δ η₀ y m g := by
    intro x
    obtain ⟨η, m, g, hη, hm, hg, -⟩ := hklt x
    obtain ⟨g', hg'⟩ := exists_isLogEqn_of_form' hn hη₀ hη hg
    obtain ⟨U, hU, hy⟩ := exists_nhds_isLogEqn' hfin hΔ.finite hg'
    exact ⟨m, g', U, hm, hU, hy⟩
  choose mm gg UU hm hU hy using h1
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (UU x : Set X))
    (fun x => (UU x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hU x⟩)
  set M := ∏ i ∈ t, mm i with hM
  have hM0 : 0 < M := Finset.prod_pos fun i _ => hm i
  have hMd : ∀ i ∈ t, mm i * (M / mm i) = M := fun i hi =>
    Nat.mul_div_cancel' (Finset.dvd_prod_of_mem _ hi)
  have sel : ∀ y : X, ∃ i ∈ t, y ∈ UU i := fun y => by
    have := ht (Set.mem_univ y)
    simpa using this
  choose s hs hsy using sel
  let e : X → X.functionFieldˣ := fun y => gg (s y) ^ (M / mm (s y))
  have he : ∀ y, ∀ w ∈ UU (s y), IsLogEqn p Δ η₀ w M (e y) := fun y w hw => by
    have := isLogEqn_pow' (hy (s y) w hw) (M / mm (s y))
    rwa [hMd _ (hs y)] at this
  let G : CartierDiv X := show cartierGroup X from
    ⟨fun y => germOf y (e y), fun x => ⟨UU (s x), hsy x, e x, fun y hy' =>
      germOf_eq_iff.2 (unitAt_of_isLogEqn' (he y y (hsy y)) (he x y hy'))⟩⟩
  refine ⟨M, G, hM0, η₀, hη₀, fun x g hg => ?_⟩
  have h0 : G.IsEqn x (e x) := rfl
  exact isLogEqn_of_unitAt' (he x x (hsy x)) (h0.iff_unitAt.1 hg)

end GlobalTheory.Discrepancy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixActionOfPadicOrderSplittingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrixAction_of_padicOrderSplitting : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (C : Type) [CommRing C] (k : ℕ), (p : C) ^ k = 0 →
  ∀ (H : Type u) [AddCommGroup H] [Module C H] (ρ : D.O →+* Module.End C H)
  (s : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])),
  ∃ Ψ : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) →+* Module.End C H,
    (∀ c, Ψ (s (c ⊗ₜ 1)) = ρ c) ∧
    (∀ T : Module.End C H, (∀ c, ρ c * T = T * ρ c) → ∀ M, Ψ M * T = T * Ψ M) ∧
    (∀ N : Submodule C H, (∀ c, ∀ x ∈ N, ρ c x ∈ N) → ∀ M, ∀ x ∈ N, Ψ M x ∈ N) ∧
    ∀ y (N : Submodule C H), (∀ a, ∀ x ∈ N, ρ (algebraMap (𝓞 D.F) D.O a) x ∈ N) → ∀ x ∈ N, Ψ (Matrix.scalar _ y) x ∈ N := by
  first | (exact @GlobalTheory.exists_matrix_action_of_splitting) | (exact GlobalTheory.exists_matrix_action_of_splitting) | (intros; apply GlobalTheory.exists_matrix_action_of_splitting  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEquivPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LabMove

theorem exists_mulEquiv_points {S K K' X : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over K} [GrpObj A] {A' : Over K'}
    [GrpObj A'] {g : K ⟶ S} {g' : K' ⟶ S} {α : A.left ⟶ G.left} {α' : A'.left ⟶ G.left}
    (h : IsGrpPullback A G g α) (h' : IsGrpPullback A' G g' α') (t : X ⟶ K) (t' : X ⟶ K')
    (f : (Over.mk t' ⊗ A').left ⟶ (Over.mk t ⊗ A).left)
    (hf₁ : f ≫ (fst (Over.mk t) A).left = (fst (Over.mk t') A').left)
    (hf₂ : f ≫ (snd (Over.mk t) A).left ≫ α = (snd (Over.mk t') A').left ≫ α') :
    ∃ e : (Over.mk t' ⟶ A') ≃* (Over.mk t ⟶ A), ∀ x', (e x').left ≫ α = x'.left ≫ α' ∧
      (ptSecT A' x').left ≫ f = (ptSecT A (e x')).left := by
  have s₁ : ∀ {B : Scheme.{0}} {T Y : Over B} (x : T ⟶ Y), (ptSecT Y x).left ≫ (fst T Y).left = 𝟙 _ := fun x => by
    rw [← Over.comp_left, ptSecT, lift_fst]; rfl
  have s₂ : ∀ {B : Scheme.{0}} {T Y : Over B} (x : T ⟶ Y), (ptSecT Y x).left ≫ (snd T Y).left = x.left := fun x => by
    rw [← Over.comp_left, ptSecT, lift_snd]
  have w : (snd (Over.mk t) A).left ≫ A.hom = (fst (Over.mk t) A).left ≫ t :=
    (Over.w (snd (Over.mk t) A)).trans (Over.w (fst (Over.mk t) A)).symm
  have w' : (snd (Over.mk t') A').left ≫ A'.hom = (fst (Over.mk t') A').left ≫ t' :=
    (Over.w (snd (Over.mk t') A')).trans (Over.w (fst (Over.mk t') A')).symm
  have hu : t' ≫ g' = t ≫ g := by
    have e := congrArg (fun q => (ptSecT A' (1 : Over.mk t' ⟶ A')).left ≫ q ≫ G.hom) hf₂
    simp only [Category.assoc] at e
    rw [h.1.w, h'.1.w, reassoc_of% w, reassoc_of% w', reassoc_of% hf₁, reassoc_of% (s₁ (1 : Over.mk t' ⟶ A')),
      reassoc_of% (s₁ (1 : Over.mk t' ⟶ A'))] at e
    exact e.symm
  obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback h t (t ≫ g) rfl
  obtain ⟨e', he'⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback h' t' (t ≫ g) hu
  have key : ∀ x', ((e'.trans e.symm) x').left ≫ α = x'.left ≫ α' := fun x' => by
    rw [← he, ← he', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  refine ⟨e'.trans e.symm, fun x' => ⟨key x', ?_⟩⟩
  have a₁ : ((ptSecT A' x').left ≫ f) ≫ (fst (Over.mk t) A).left =
      (ptSecT A ((e'.trans e.symm) x')).left ≫ (fst (Over.mk t) A).left := by
    rw [Category.assoc, hf₁, s₁, s₁]; rfl
  have a₂ : ((ptSecT A' x').left ≫ f) ≫ (snd (Over.mk t) A).left =
      (ptSecT A ((e'.trans e.symm) x')).left ≫ (snd (Over.mk t) A).left := by
    refine h.1.hom_ext ?_ ?_
    · rw [s₂, key, Category.assoc, Category.assoc, hf₂, reassoc_of% (s₂ x')]
    · rw [Category.assoc, w, Category.assoc _ _ A.hom, w, ← Category.assoc, a₁, Category.assoc]
  exact pullback.hom_ext a₁ a₂

end GlobalTheory.Mum.LabMove

namespace GlobalTheory.Mum

theorem Trait.exists_lab_push : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → (∀ x : TFK (R := W) F ⟶ T.A.A, x ^ (C.n ^ j) = 1 ↔ ∃ p', lab' p' = x) → ∃ lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A), LabExt em (C.lab j) lab ∧ (∀ x : TFK (R := R) F ⟶ C.A.A, x ^ (C.n ^ j) = 1 ↔ ∃ p, lab p = x) ∧ ∀ (p : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), p'.y = T.hD.xe.symm p.y → IsPullGtF T.φ T.hD F p.g p'.g → (ptSecT T.A.A (lab' p')).left ≫ f = (ptSecT C.A.A (lab p)).left := by
  intro R _ _ _ _ D C j W _ _ _ T F _ _ _ _ em hF f _ hf₁ hf₂ lab' hext honto
  have := T.U.gen_hom
  have : IsMonHom T.U.gen.symm.hom := by show IsMonHom T.U.gen.inv; infer_instance
  have gT : IsGrpPullback T.A.A C.G (jK W ≫ T.ξ) (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) :=
    ((isGrpPullback_of_iso T.U.gen.symm).comp ((isGrpPullback_pullback T.G (jK W)).comp T.cart)).congr
      (Category.id_comp _) rfl
  obtain ⟨e, he⟩ := LabMove.exists_mulEquiv_points C.α_cart gT (jFK (R := R) F) (jFK (R := W) F) f hf₁ hf₂
  let P : QkPt D.toPre F (C.n ^ j) → QkPt T.D'.toPre F (C.n ^ j) :=
    GlobalTheory.ArcPull.pullQk T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  have hP : ∀ p p', p' = P p ↔ p'.y = T.hD.xe.symm p.y ∧ IsPullGtF T.φ T.hD F p.g p'.g :=
    GlobalTheory.ArcPull.eq_pullQk_iff T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  have hs : Function.Surjective P :=
    GlobalTheory.ArcPull.pullQk_surjective T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  refine ⟨fun p => e (lab' (P p)), fun p p₁ hp => ?_, fun x => ?_, fun p p' hy hg => ?_⟩
  · refine C.α_cart.1.hom_ext ?_ ?_
    · rw [Category.assoc]
      exact (he _).1.trans (hext p p₁ (P p₁) hp ((hP _ _).1 rfl).1 ((hP _ _).1 rfl).2)
    · rw [Category.assoc, Over.w, Over.w]
      simp only [TFK, Over.mk_hom, jFK]
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp
  · obtain ⟨x', rfl⟩ := e.surjective x
    rw [← map_pow, MulEquiv.map_eq_one_iff, honto, hs.exists]
    exact exists_congr fun p => e.injective.eq_iff.symm
  · obtain rfl := (hP p p').2 ⟨hy, hg⟩
    exact (he _).2

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoTwoHomNormalisedAtOrigin
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

theorem exists_lamVal_origin_two : ∀ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B] (M₀ : LB B₀.left) (M : LB B.left), M₀.IsLB → M.IsLB → ∀ (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b], LBIso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left) → ∃ w : LB.Iso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left), w.IsGen ∧ ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1 := by
  intro S B₀ B _ _ _ _ M₀ M hM₀ hM a b _ _ H
  obtain ⟨w₀, hw₀⟩ := H
  let F : (G2 B₀).left ⟶ (G2 B).left := (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left
  let e : (𝟙_ (Over S)).left ⟶ (G2 B₀).left := (lift (1 : 𝟙_ (Over S) ⟶ B₀) 1).left
  let q : (𝟙_ (Over S)).left ⟶ B.left := (1 : 𝟙_ (Over S) ⟶ B).left
  let q' : (𝟙_ (Over S)).left ⟶ B₀.left := (1 : 𝟙_ (Over S) ⟶ B₀).left
  have eF : e ≫ F = (lift (1 : 𝟙_ (Over S) ⟶ B) 1).left := by
    show (lift (1 : 𝟙_ (Over S) ⟶ B₀) 1 ≫ lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b)).left = _
    rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, MonObj.one_comp]
  have hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ F) ≫ (psum B (x2 B) I.down).left = q := fun I => by
    rw [eF]
    exact congrArg (fun z => z.left) (GlobalTheory.PolDeg.NormIso.lift_one_psum B (T := 𝟙_ (Over S)) I.down)
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum B₀ (x2 B₀) I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (GlobalTheory.PolDeg.NormIso.lift_one_psum B₀ (T := 𝟙_ (Over S)) I.down)
  obtain ⟨w, hw, hv⟩ := GlobalTheory.PolDeg.NormIso.exists_normalised M M₀ hM hM₀ (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B (x2 B) I.down).left) (fun I => (psum B₀ (x2 B₀) I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) F e (toUnit (G2 B₀)).left
    (congrArg (fun z => z.left) (toUnit_unique (lift (1 : 𝟙_ (Over S) ⟶ B₀) 1 ≫ toUnit (G2 B₀)) (𝟙 _))) q q' hq hq'
    w₀ hw₀
  refine ⟨w, hw, fun T z J J' hJ hJ' => ?_⟩
  have hp : (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left = (toUnit T).left ≫ e := by
    show _ = (toUnit T ≫ lift (1 : 𝟙_ (Over S) ⟶ B₀) 1).left
    rw [comp_lift, MonObj.comp_one]
  have key : ∀ (p : T.left ⟶ (G2 B₀).left) (j : (abelian₂ B M).ι) (k : (abelian₂ B₀ M₀).ι),
      (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ F ≫ (psum B (x2 B) I.down).left)) = j →
      (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum B₀ (x2 B₀) I.down).left)) = k →
      GlobalTheory.PolDeg.lamVal w p z J J' = gw (L := abelian₂ B M) (L' := abelian₂ B₀ M₀) w p z j k := by
    rintro p _ _ rfl rfl
    rfl
  rw [hp]
  refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
    (funext fun I => ?_)).trans (hv T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
  · rw [← hq I, Category.assoc, Category.assoc]
  · rw [← hq' I, Category.assoc]

end GlobalTheory.Mum.Two
end
end

