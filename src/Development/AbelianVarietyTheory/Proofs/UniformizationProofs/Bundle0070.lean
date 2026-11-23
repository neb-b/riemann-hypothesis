module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTwistedSectionOfCompatibleLevels
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePower
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.BaseExpansionExists

section General
variable {X X₁ X₂ Y Y' Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {K : Type} [Fintype K]

theorem exists_pull {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (e : ∀ i, φ' i = h ≫ φ i)
    (s : LB.Sec (LB.LinComb L φ ε)) : ∃ s' : LB.Sec (LB.LinComb L φ' ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J, Good L z J → sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : φ' = fun i => h ≫ φ i := funext e
  exact ⟨_, fun Z r z J hJ => H1.SectionArithmetic.sval_pullSec s h r z hJ⟩

theorem exists_carry (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (k : ℕ)
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => f₁) (fun _ => (k : ℤ)))) :
    ∃ τ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J₁ J₂, Good L₁ z J₁ → Good L₂ z J₂ →
        sval τ r z J₂ = (gw w r z (J₂ (r ≫ f₂)) (fun _ => J₁ (r ≫ f₁))).val ^ k * sval s r z J₁ := by
  obtain ⟨τ, hτ⟩ := GenericFibreSections.exists_transfer hL₁ hL₂ f₁ f₂ k
    (fun i j => (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))
    (fun i j y hi hj => ⟨mem_pull.2 hj, mem_pull.2 hi⟩)
    (fun i j => (show Γ(Y, (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))ˣ from
      w.s (fun _ => j, fun _ => i)) ^ k) (fun y i i' j j' hi hi' hj hj' => by
      have e := GenericFibreSections.gw_trans hw y hi hi' hj hj'
      rw [map_pow, map_pow, zpow_natCast, zpow_natCast, ← mul_pow, ← mul_pow]
      exact congrArg (· ^ k) e) s
  refine ⟨τ, fun Z r z J₁ J₂ h₁ h₂ => ?_⟩
  rw [hτ Z r z J₁ J₂ h₁ h₂, map_pow, Units.val_pow_eq_pow_val]
  rfl

theorem sval_zero {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0)
    (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans
    ((congrArg _ (map_zero _)).trans (map_zero _)))

theorem zero_of_sval (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans ((gs_eq (𝟙 Y) y _ hy _).trans ((congrArg _ (map_zero _)).trans (map_zero _))).symm

theorem sval_eq_of_id {Y₁ : Scheme.{0}} {K' : Type} [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y₁ ⟶ X)} {ε' : K' → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} {s' : LB.Sec (LB.LinComb L φ' ε')}
    {p : Y' ⟶ Y} {p' : Y' ⟶ Y₁} (h : ∀ y J, Good L y J → sval s p y J = sval s' p' y J)
    (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) : sval s (r ≫ p) z J = sval s' (r ≫ p') z J := by
  obtain ⟨h₀, h₁, -⟩ := values_natural X Y Y' Z L K φ ε p r z J hJ
  obtain ⟨-, h₂, -⟩ := values_natural X Y₁ Y' Z L K' φ' ε' p' r z J hJ
  rw [h₁, h₂, h _ _ h₀]

theorem sum_of_id {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {N : Type} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ₁ : N → K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {φ₂ : N → K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {τ : LB.Sec (LB.LinComb L φ ε)} {f : ∀ α, LB.Sec (LB.LinComb L (φ₁ α) ε₁)}
    {t : ∀ α, LB.Gen (LB.LinComb L (φ₂ α) ε₂)} {q : Y ⟶ Y'} {S : Finset N}
    (h : ∀ y J, Good L y J → sval τ (𝟙 Y) y J = ∑ α ∈ S, sval (f α) q y J * (val (t α) (𝟙 Y) y J).val)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval τ r z J = ∑ α ∈ S, sval (f α) (r ≫ q) z J * (val (t α) r z J).val := by
  obtain ⟨h₀, h₁, -⟩ := values_natural X Y Y Z L K φ ε (𝟙 Y) r z J hJ
  have a := h₁ τ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Category.comp_id, h _ _ h₀, map_sum] at a
  refine a.trans (Finset.sum_congr rfl fun α _ => ?_)
  have b := (values_natural X Y' Y Z L K₁ (φ₁ α) ε₁ q r z J hJ).2.1 (f α)
  have c := (values_natural X Y Y Z L K₂ (φ₂ α) ε₂ (𝟙 Y) r z J hJ).2.2.1 (t α)
  rw [Category.comp_id] at c
  rw [map_mul, b, c]

end General

section Levels
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

omit [GrpObj G] [IsCommMonObj G] in
theorem thickMap_fst (e : ℕ) : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem thickMap_prBe (e : ℕ) : thickMap R I e D.P.A ≫ (D.prBe I (e + 1)).left = (D.prBe I e).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem q_thickMap (U : PreU I D A G) (e : ℕ) :
    (U.gt e).q.left ≫ thickMap R I e D.P.A = thickMap R I e G ≫ (U.gt (e + 1)).q.left := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg ((U.gt e).q.left ≫ ·) (thickMap_prBe e)).trans
      ((U.gt_q e).symm.trans (Category.assoc _ _ _).symm))
  · have a : (U.gt e).q.left ≫ pullback.snd D.P.A.hom (thick R I e) = pullback.snd G.hom (thick R I e) :=
      Over.w (U.gt e).q
    have b : (U.gt (e + 1)).q.left ≫ pullback.snd D.P.A.hom (thick R I (e + 1)) =
      pullback.snd G.hom (thick R I (e + 1)) := Over.w (U.gt (e + 1)).q
    have c : ∀ H : Over (Spec (CommRingCat.of R)), thickMap R I e H ≫ pullback.snd H.hom (thick R I (e + 1)) =
      pullback.snd H.hom (thick R I e) ≫ thickTrans R I e := fun H => pullback.lift_snd _ _ _
    exact (Category.assoc _ _ _).trans ((congrArg ((U.gt e).q.left ≫ ·) (c _)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ thickTrans R I e) a).trans ((c G).symm.trans
        ((congrArg (thickMap R I e G ≫ ·) b.symm).trans (Category.assoc _ _ _).symm)))))

theorem famφT_eq (T : Over (Spec (CommRingCat.of R))) (α : D.X) (i : Fin 4) :
    famφT D T α i = (snd T D.P.A).left ≫ D.famφB α i := by
  fin_cases i
  · exact (Category.comp_id _).symm
  · show (padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (snd T D.P.A ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    congr 1
    rw [padd, padd, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  · show (toUnit (T ⊗ D.P.A) ≫ D.c α).left = (snd T D.P.A ≫ toUnit D.P.A ≫ D.c α).left
    congr 1
    simp
  · show (toUnit (T ⊗ D.P.A) ≫ η[D.P.A]).left = (snd T D.P.A ≫ toUnit D.P.A ≫ η[D.P.A]).left
    congr 1
    simp

end Levels

theorem main : Laws → Laws2 → (AllPre fun U => ∀ k, 1 ≤ k → ∀ σ, ∃ f, U.ExpT (𝟙_ _) k σ f) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U k hk σ
  have hB := D.P.isLB
  have hG := U.P.L.isLB
  have lam : (snd (𝟙_ _) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ G).inv.left ≫ (snd (𝟙_ _) G).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]

  have lev : ∀ e : ℕ, ∃ τ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => (U.gt e).pG.left) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left) (z : Z) JG J,
        Good U.P.L.L z JG → Good D.P.L z J →
        sval τ r z J = (gw (U.w e) r z (J (r ≫ (U.gt e).pG.left))
          (fun _ => JG (r ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left))).val ^ k *
          sval σ ((r ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left) ≫ (λ_ G).inv.left) z JG := fun e => by
    obtain ⟨s, hs⟩ := exists_pull (φ' := fun _ : Fin 1 => (fstG (IsLocalRing.maximalIdeal V) e G).left)
      ((fstG (IsLocalRing.maximalIdeal V) e G).left ≫ (λ_ G).inv.left)
      (fun _ => by rw [Category.assoc, lam', Category.comp_id]) σ
    obtain ⟨τ, hτ⟩ := exists_carry hG hB (U.w e) (U.w_gen e) k s
    refine ⟨τ, fun Z r z JG J hJG hJ => (hτ Z r z JG J hJG hJ).trans (congrArg _ ((hs Z r z JG hJG).trans ?_))⟩
    exact congrArg (fun p => sval σ p z JG) (Category.assoc _ _ _).symm
  choose τ hτ using lev
  have ex := fun e => GlobalTheory.T.existsUnique_thickTorus_level_weight_expansion V _ D e G (U.gt e) k (τ e)
  choose f hf hu using ex
  choose S hS hsum using hf

  have compat : ∀ α e z J, Good D.P.L z J →
      sval (f (e + 1) α) (thickMap V _ e D.P.A) z J = sval (f e α) (𝟙 _) z J := by
    intro α e
    choose f' hf' using fun β => exists_pull
      (φ' := fun i => (D.prBe (IsLocalRing.maximalIdeal V) e).left ≫ D.famφB β i) (thickMap V _ e D.P.A)
      (fun i => ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.famφB β i) (thickMap_prBe e))).symm) (f (e + 1) β)
    have E : f' = f e := by
      refine hu e f' ⟨S (e + 1), fun β hβ => zero_of_sval hB fun y J hJ =>
        (hf' β _ _ y J hJ).trans (sval_zero (hS _ β hβ) _ hJ), fun z J hJ => ?_⟩
      obtain ⟨JG, hJG⟩ := exists_good_pt hG z
      have a := sum_of_id (hsum (e + 1)) (thickMap V _ e G) z hJ
      have b : sval (τ e) (𝟙 (thickObj V (IsLocalRing.maximalIdeal V) e G).left) z J =
          sval (τ (e + 1)) (thickMap V _ e G) z J := by
        refine (hτ e _ _ z JG J hJG hJ).trans (Eq.trans ?_ (hτ (e + 1) _ _ z JG J hJG hJ).symm)
        have c := U.w_compat e _ (𝟙 _) z _ _ (hJ (U.gt e).pG.left) (hJG (fstG (IsLocalRing.maximalIdeal V) e G).left)
        rw [Category.id_comp] at c
        rw [U.gt_q, thickMap_fst, c]
        simp only [Category.id_comp]
      refine b.trans (a.trans (Finset.sum_congr rfl fun β _ => congrArg₂ (· * ·) ?_ (congrArg Units.val ?_)))
      · exact (congrArg (fun p => sval (f (e + 1) β) p z J) (q_thickMap U e).symm).trans (hf' β _ _ z J hJ).symm
      · exact ((congrArg (fun p => val ((U.gt (e + 1)).t β) p z J) (Category.id_comp _).symm).trans
          (val_pull hJ _ _ _).symm).trans (val_corr hJ (U.gt_t e β) _)
    intro z J hJ
    rw [← E]
    exact ((hf' α _ _ z J hJ).trans (congrArg (fun p => sval (f (e + 1) α) p z J) (Category.id_comp _))).symm
  choose s hs _ using fun α => _root_.GlobalTheory.SecLimit.existsUnique_sec_of_compatible h1 h2 V hV D k hk α (fun e => f e α) (compat α)
  choose F hF using fun α => exists_pull (snd (𝟙_ _) D.P.A).left (famφT_eq (𝟙_ _) α) (s α)
  refine ⟨F, fun e => ⟨S e, fun Z x rG rB hrG hrB _ z JG J hJG hJ => ?_⟩⟩
  have v : ∀ α, sval (F α) rB z J = sval (f e α) (x ≫ (U.gt e).q.left) z J := fun α => by
    refine (hF α _ _ z J hJ).trans ?_
    have a := sval_eq_of_id (hs α e) (x ≫ (U.gt e).q.left) z hJ
    refine Eq.trans (congrArg (fun p => sval (s α) p z J) (hrB.trans (Category.assoc _ _ _).symm)) (a.trans ?_)
    exact congrArg (fun p => sval (f e α) p z J) (Category.comp_id _)
  refine ⟨fun α hα => (v α).trans (sval_zero (hS e α hα) _ hJ), ?_⟩
  have r : rG = (x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left) ≫ (λ_ G).inv.left := by
    rw [← hrG, Category.assoc, lam, Category.comp_id]
  rw [r]
  refine (hτ e _ x z JG J hJG hJ).symm.trans ((sum_of_id (hsum e) x z hJ).trans ?_)
  exact Finset.sum_congr rfl fun α _ => congrArg (· * _) (v α).symm

end GlobalTheory.BaseExpansionExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenOfIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.Transl

section General
variable {X X' W Y Y₂ : Scheme.{0}} {L : LB X} {L' : LB X'} {K : Type} [Fintype K]

theorem exists_gen_of_iso (hL : L.IsLB) (hL' : L'.IsLB) {F : W ⟶ X} {F' : W ⟶ X'}
    (w : LB.Iso (L'.pull F') (L.pull F)) (hw : w.IsGen) (y : K → (Y ⟶ W)) (h : Y ⟶ Y₂) {φ : K → (Y₂ ⟶ X)}
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (ha : ∀ k, y k ≫ F' = φ' k) (hb : ∀ k, y k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (J'), Good L z J →
      Good L' z J' → val t (r ≫ h) z J =
        (∏ k, gw w (r ≫ y k) z (J ((r ≫ y k) ≫ F)) (fun _ => J' ((r ≫ y k) ≫ F')) ^ ε k) * val a r z J' := by
  obtain rfl : (fun k => y k ≫ F') = φ' := funext ha
  obtain ⟨a, ga, H⟩ := CubTransport.exists_pmaps ((isGen_iff w).1 hw) hL (pull_isLB hL' F') (φ' := y) h hb t ht
  have le : ∀ j : K → L'.ι, LB.wchart L' (fun k => y k ≫ F') j ≤ LB.wchart (L'.pull F') y (fun k _ => j k) :=
    fun j p hp => Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hp k)
  refine ⟨⟨fun j => res (le j) (a.s fun k _ => j k)⟩, isGen_of_gm _ fun p j j' hj hj' => ?_,
    fun Z r z J J' hJ hJ' => ?_⟩
  · refine (gm_res _ p (le j) hj _).trans ((gen_trans ga (𝟙 Y) p (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res _ p (le j') hj' _).symm))
    refine (gm_pull_g L' F' (𝟙 Y ≫ y k) p _ _ (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans ?_
    rw [Category.assoc]
  · have g' : Good (L'.pull F') z (fun ψ _ => J' (ψ ≫ F')) := fun ψ => mem_pull.2 (hJ' (ψ ≫ F'))
    refine (CubTransport.val_pmaps hb H r hJ g').trans (congrArg (_ * ·) ?_)
    rw [val_of _ r z J' (fun k => J' ((r ≫ y k) ≫ F')) (fun k => by rw [Category.assoc])]
    exact (gm_res r z (le _) (Set.mem_iInter.2 fun k => hJ' ((r ≫ y k) ≫ F')) _).symm

theorem exists_unit_base {S₀ : Scheme.{0}} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) (a : Γ(Y, ⊤)ˣ) :
    ∃ c : Γ(S₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), gm r z ⊤ a = gm (r ≫ p) z ⊤ c := by
  obtain ⟨c, hc⟩ := hp a.val
  have e₁ : e.appTop.hom a.val = c := by
    rw [← hc, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]; simp
  refine ⟨Units.map e.appTop.hom.toMonoidHom a, fun Z r z => ?_⟩
  refine Eq.trans (congrArg (gm r z ⊤) (Units.ext ?_)) (gm_pull r p z ⊤ trivial _)
  exact hc.symm.trans (congrArg p.appTop.hom e₁.symm)

theorem surj_fst (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (fst T A).left.appTop.hom := by
  have e : (fst T A).left = (β_ T A).hom.left ≫ (snd A T).left := by
    rw [← Over.comp_left, braiding_hom_snd]
  rw [e]
  have : IsIso (β_ T A).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (β_ T A).hom))
  have : IsIso (β_ T A).hom.left.appTop := inferInstanceAs (IsIso ((β_ T A).hom.left.app ⊤))
  exact surj_comp (ConcreteCategory.bijective_of_isIso (β_ T A).hom.left.appTop).2 (surj_snd hG hA T)

def comb {M : LB Y} (a : Γ(Y, ⊤)) (s t : LB.Sec M) : LB.Sec M where
  f j := (Y.presheaf.map (homOfLE le_top).op).hom a * s.f j + t.f j
  compat i j := by
    have e : ∀ {V : Y.Opens} (h : M.U i ⊓ M.U j ≤ V), (Y.presheaf.map (homOfLE h).op).hom
        ((Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a) = (Y.presheaf.map (homOfLE le_top).op).hom a :=
      fun h => by rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [map_add (f := _), map_add (f := _), map_mul, map_mul, e, e, s.compat i j, t.compat i j]
    ring

def zeroSec (M : LB Y) : LB.Sec M where
  f _ := 0
  compat i j := by rw [map_zero, map_zero, mul_zero]

theorem sval_zeroSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) :
    sval (zeroSec (LB.LinComb L φ ε)) r z J = 0 := by
  unfold sval gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem gs_scal {R : Type} [CommRing R] {Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (c : R) : gs r z ⊤ (scal p c) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) :=
  gs_pull r p z ⊤ trivial _

end General

theorem cubN_twist {A B C U : Type} [CommGroup A] [CommGroup B] [CommGroup C] [CommGroup U] (β : A →* B) (κ : A →* C)
    (W : A → U) {θ : B → B → B → U} {θ' : C → C → C → U}
    (h : ∀ a b c, θ (β a) (β b) (β c) * W (a * b) * W (a * c) * W (b * c) * W 1 =
      W (a * b * c) * W a * W b * W c * θ' (κ a) (κ b) (κ c)) {N : ℕ} {m : A} (hm : m ^ N = 1) (y : A) :
    cubN θ N 1 (β m) (β y) * W (m * y) ^ N * W 1 ^ N = W y ^ N * W m ^ N * cubN θ' N 1 (κ m) (κ y) := by
  have key : ∀ n : ℕ, cubN θ n 1 (β m) (β y) * W (m ^ n) * W y * W (m * y) ^ n * W 1 ^ n =
      W (m ^ n * y) * W 1 * W y ^ n * W m ^ n * cubN θ' n 1 (κ m) (κ y) := by
    intro n
    induction n with
    | zero => simp [cubN, mul_comm]
    | succ n ih =>
      have c := h (m ^ n) m y
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, map_pow, ← pow_succ m] at ih c ⊢
      simp only [pow_succ (W _)]
      apply Additive.ofMul.injective
      have ih' := congrArg Additive.ofMul ih
      have c' := congrArg Additive.ofMul c
      simp only [ofMul_mul] at ih' c' ⊢
      linear_combination (norm := abel) ih' + c'
  have k := key N
  rw [hm, _root_.one_mul y] at k
  apply Additive.ofMul.injective
  have k' := congrArg Additive.ofMul k
  simp only [ofMul_mul] at k' ⊢
  linear_combination (norm := abel) k'

section Theta
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)

theorem exists_thetaGen {T : Over S} (x : T ⟶ G) {N : ℕ} (hx : x ^ N = 1)
    (f : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(1 : T ⟶ G).left, x.left] ![(N : ℤ), -(N : ℤ)])) (hf : f.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T G).left, ((fst T G ≫ x) * snd T G).left] ![(N : ℤ), -(N : ℤ)]),
      t.IsGen ∧ ∀ (T' : Over S) (τ : T' ⟶ T) (y : T' ⟶ G) (z : T'.left) (J), Good L.L z J →
        val t (lift τ y).left z J = cubN (cubV c z J) N 1 (τ ≫ x) y * val f τ.left z J := by
  obtain ⟨n, hn, vn⟩ := exists_cubN c 1 (fst T G ≫ x) (snd T G) N
  have hm : (fst T G ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨t, ht, vt⟩ := exists_gen L.isLB (φ' := ![(snd T G).left, ((fst T G ≫ x) * snd T G).left])
    (ε' := ![(N : ℤ), -(N : ℤ)]) (fun U _ h => by
      have q : (fst T G).left ≫ (1 : T ⟶ G).left = (1 : T ⊗ G ⟶ G).left :=
        congrArg (fun q : T ⊗ G ⟶ G => q.left) (MonObj.comp_one (M := G) (fst T G))
      have p : ∏ k : Fin 2, h ((fst T G).left ≫ ![(1 : T ⟶ G).left, x.left] k) ^ (![(N : ℤ), -(N : ℤ)] k) =
          h (1 : T ⊗ G ⟶ G).left ^ (N : ℤ) * h (fst T G ≫ x).left ^ (-(N : ℤ)) := by
        rw [Fin.prod_univ_two, ← q]; rfl
      refine (DVR.prod_sum₂ (K := Fin 8) (K' := Fin 2) (U := U) _ rfl p).trans ?_
      rw [hm]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen L.L _ _ _ _ n (LB.pullGen L.L _ _ f (fst T G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hn (DVR.pullGen_isGen _ _ _ _ hf _))
  refine ⟨t, ht, fun T' τ y z J hJ => ?_⟩
  refine (vt _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((vn T' _ z J hJ).trans ?_)
    ((val_pull hJ _ _ _).trans ?_)))
  · rw [MonObj.comp_one, lift_fst_assoc, lift_snd]
  · rw [← Over.comp_left, lift_fst]

end Theta

section ThetaSec
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem exists_translSec (hL : L.IsLB) {T : Over S} (x : T ⟶ G) {N : ℤ}
    (t : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T G).left, ((fst T G ≫ x) * snd T G).left] ![N, -N]))
    (ht : t.IsGen) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (𝟙_ _) G).left) (fun _ => N))) :
    ∃ σ' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => N)),
      ∀ (T' : Over S) (τ : T' ⟶ T) (y : T' ⟶ G) (z : T'.left) (J), Good L z J →
        sval σ' (lift τ y).left z J =
          sval σ (lift (toUnit T') ((τ ≫ x) * y)).left z J * (val t (lift τ y).left z J).val := by
  obtain ⟨σ', v⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T G).left) (ε' := fun _ => N) (fun U _ h => by
      have q : (lift (toUnit (T ⊗ G)) ((fst T G ≫ x) * snd T G)).left ≫ (snd (𝟙_ _) G).left =
          ((fst T G ≫ x) * snd T G).left := by rw [← Over.comp_left, lift_snd]
      refine (DVR.prod_sum₂ (K := Fin 1) (K' := Fin 2) (U := U) _ (Fin.prod_univ_one _) (Fin.prod_univ_two _)).trans ?_
      rw [Fin.prod_univ_one]
      show h (_ ≫ _) ^ N * (h (snd T G).left ^ N * h ((fst T G ≫ x) * snd T G).left ^ (-N)) = _
      rw [q, zpow_neg, mul_left_comm, mul_inv_cancel, _root_.mul_one])
    (pullMulSec σ (lift (toUnit (T ⊗ G)) ((fst T G ≫ x) * snd T G)).left t ht)
  refine ⟨σ', fun T' τ y z J hJ => (v _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)⟩
  rw [← Over.comp_left, comp_lift, MonObj.comp_mul, lift_fst_assoc, lift_snd, toUnit_unique (_ ≫ _) (toUnit T')]

end ThetaSec

section Base
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
open ReciprocityTheory.ChartRestriction.G.DVR

theorem prod_famT {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T ⊗ D.P.A) (α : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ famφT D T α i) ^ DegPre.famε k i =
      h (ρ ≫ snd _ _).left ^ ((k : ℤ) - 1) * h (cP D T' α * (ρ ≫ snd _ _)).left * (h (cP D T' α).left)⁻¹ *
        h (1 : T' ⟶ D.P.A).left := by
  have e₁ : ρ.left ≫ famφT D T α 1 = (cP D T' α * (ρ ≫ snd _ _)).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (snd _ _) (cP D _ α)).trans (by rw [comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ famφT D T α 2 = (cP D T' α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₃ : ρ.left ≫ famφT D T α 3 = (1 : T' ⟶ D.P.A).left :=
    congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

def fac {T T' : Over (Spec (CommRingCat.of R))} (g : GtPt D T) (N : ℕ)
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(1 : T ⟶ D.P.A).left, g.b.left] ![(N : ℤ), -(N : ℤ)])) (α : D.X)
    (τ : T' ⟶ T) (y : T' ⟶ D.P.A) (z : T'.left) (J : (T'.left ⟶ D.P.A.left) → D.P.L.ι) :
    (T'.left.presheaf.stalk z)ˣ :=
  cubN (th D z J) N 1 (τ ≫ g.b) y * val w τ.left z J * val (g.s α) τ.left z J *
    (th D z J (cP D T' α) (τ ≫ g.b) y)⁻¹

theorem exists_translFam {T : Over (Spec (CommRingCat.of R))} (g : GtPt D T) {N : ℕ} (hb : g.b ^ N = 1)
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(1 : T ⟶ D.P.A).left, g.b.left] ![(N : ℤ), -(N : ℤ)]))
    (hw : w.IsGen) (α : D.X) (f : SecBT D (𝟙_ _) N α) :
    ∃ f' : SecBT D T N α, ∀ (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ D.P.A) (z : T'.left) (J),
      Good D.P.L z J → sval f' (lift τ y).left z J =
        sval f (lift (toUnit T') ((τ ≫ g.b) * y)).left z J * (fac g N w α τ y z J).val := by
  obtain ⟨t, ht, vt⟩ := exists_thetaGen D.cub g.b hb w hw
  let a : T ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let m : T ⊗ D.P.A ⟶ D.P.A := fst _ _ ≫ g.b
  let x : T ⊗ D.P.A ⟶ D.P.A := snd _ _
  let u := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t (LB.pullGen D.P.L _ _ (g.s α) (fst T D.P.A).left))
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift m x)).left))
  have hu : u.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ ht (pullGen_isGen _ _ _ _ (g.isGen α) _))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))
  obtain ⟨f', v⟩ := exists_sec D.P.isLB (φ' := famφT D T α) (ε' := DegPre.famε N) (fun U _ h => by
      have p₁ := prod_cub a m x h
      have p₂ := FormalPoint.prod_gtφT (fst T D.P.A) g.b α h
      have p₃ := prod_famT (𝟙 (T ⊗ D.P.A)) α N h
      have p₄ := prod_famT (lift (toUnit (T ⊗ D.P.A)) (m * x)) α N h
      have p₅ : ∏ k : Fin 2, h (![x.left, (m * x).left] k) ^ (![(N : ℤ), -(N : ℤ)] k) =
          h x.left ^ (N : ℤ) * h (m * x).left ^ (-(N : ℤ)) := Fin.prod_univ_two _
      simp only [Over.id_left, Category.id_comp] at p₃
      rw [lift_snd, ← _root_.mul_assoc (cP D _ α)] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := (Fin 2 ⊕ Fin 4) ⊕ thK) (U := U) _ p₄
        (prod_sum₂ (K := Fin 2 ⊕ Fin 4) (K' := thK) (U := U) _
          (prod_sum₂ (K := Fin 2) (K' := Fin 4) (U := U) _ p₅ p₂) (prod_neg _ _ p₁))) (Eq.trans ?_ p₃.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, a, m, x]
      module)
    (pullMulSec f (lift (toUnit (T ⊗ D.P.A)) (m * x)).left u hu)
  refine ⟨f', fun T' τ y z J hJ => (v _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)⟩
  have e : val u (lift τ y).left z J = fac g N w α τ y z J := by
    refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (vt T' τ y z J hJ) ((val_pull hJ _ _ _).trans ?_))) ((val_inv _ _).trans (congrArg (·⁻¹)
      ((val_cub D.cub (lift τ y) hJ _ _ _).trans ?_))))
    · rw [← Over.comp_left, lift_fst]
    · rw [comp_cP, lift_fst_assoc, lift_snd]
  rw [e, ← Over.comp_left, comp_lift, MonObj.comp_mul, lift_fst_assoc, lift_snd, toUnit_unique (_ ≫ _) (toUnit T')]

end Base

end GlobalTheory.UU.Transl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPsiRelationOfPullbackExtensionField
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psiRel_of_pullB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (f : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1), PullB D F (toUnit _) 1 f s₀ → PsiRel D (𝟙_ _) f → PsiRel D (TF (R := R) F) s₀ := by
  intro R _ _ D F _ _ f s₀ h hψ χ T ρ κ y z J hJ
  have a := pullB_values R D F _ _ 1 f s₀ h χ T ρ y z J hJ
  have b := pullB_values R D F _ _ 1 f s₀ h 0 T ρ (y * cT D T χ) z J hJ
  have c := hψ χ T (ρ ≫ toUnit _) κ y z J hJ
  exact a.trans (c.trans (congrArg _ b.symm))

end GlobalTheory
end

