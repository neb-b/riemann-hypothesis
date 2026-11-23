module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSupportPairIffDegreeTwoSumDiff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismOfMultiplicativeSectionFamily
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SectionAut

abbrev PP {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (a : ℤ) : LB Y :=
  LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => a)

theorem mem_one {X Y : Scheme.{0}} {L : LB X} {p : Y ⟶ X} {j : Fin 1 → L.ι} {y : Y} :
    y ∈ LB.wchart L (fun _ : Fin 1 => p) j ↔ p y ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem exists_equiv {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N n : ℕ) :
    ∃ E : H0 (PP L p N) n ≃ LB.Sec (PP L p ((N * n : ℕ) : ℤ)),
      ∀ a (j : Fin 1 → L.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart L (fun _ : Fin 1 => p) j →
        gs r z (LB.wchart L (fun _ : Fin 1 => p) j) ((E a).f j) =
          gs r z (LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j)) (a.f (fun _ => j)) := by
  obtain ⟨E, hE⟩ := PowSections.exists_equiv L p N n
  refine ⟨E, fun a j Z r z hz => ?_⟩
  have le : LB.wchart L (fun _ : Fin 1 => p) j ≤ LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) :=
    fun y hy => Set.mem_iInter.2 fun _ => hy
  have e : (E a).f j = (Y.presheaf.map (homOfLE le).op).hom (a.f (fun _ => j)) :=
    fn_ext fun y hy => (hE a j y (mem_one.1 hy)).trans (gs_res (𝟙 Y) y le hy _).symm
  exact (congrArg (gs r z _) e).trans (gs_res r z le hz _)

theorem exists_gen_of_iso {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N n : ℕ) (F ψ : Y ⟶ Y) (hψ : ψ ≫ F = 𝟙 Y)
    (m : Y ⟶ X) (hm : ψ ≫ p = m) (w : LB.Iso (PP L p N) ((PP L p N).pull F)) (hw : w.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![p, m] ![((N * n : ℕ) : ℤ), -((N * n : ℕ) : ℤ)]), α.IsGen ∧
      ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, m] j →
        gm (𝟙 Y) y (LB.wchart L ![p, m] j) (α.s j) = Geo.Tor.gw w ψ y (fun _ => j 0) (fun _ => j 1) ^ (n : ℤ) := by
  subst hm
  have hF : ∀ y, F (ψ y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, hψ]; rfl
  have h0 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, ψ ≫ p] j →
      F (ψ y) ∈ (PP L p N).U (fun _ => j 0) := fun j y hy => by
    rw [hF]; exact mem_one.2 (Set.mem_iInter.1 hy 0)
  have h1 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, ψ ≫ p] j →
      ψ y ∈ (PP L p N).U (fun _ => j 1) := fun j y hy => mem_one.2 (Set.mem_iInter.1 hy 1)
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L ![p, ψ ≫ p] j ≤
      ψ ⁻¹ᵁ (((PP L p N).pull F).U (fun _ _ => j 0) ⊓ (PP L p N).U (fun _ => j 1)) := fun j y hy =>
    ⟨mem_pull.2 (h0 j y hy), h1 j y hy⟩
  let α : LB.Gen (LB.LinComb L (K := Fin 2) ![p, ψ ≫ p] ![((N * n : ℕ) : ℤ), -((N * n : ℕ) : ℤ)]) :=
    ⟨fun j => res (le j) (pullU ψ _ (w.s (fun _ _ => j 0, fun _ => j 1))) ^ (n : ℤ)⟩
  have hα : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, ψ ≫ p] j →
      gm (𝟙 Y) y (LB.wchart L ![p, ψ ≫ p] j) (α.s j) =
        Geo.Tor.gw w ψ y (fun _ => j 0) (fun _ => j 1) ^ (n : ℤ) := fun j y hy =>
    (map_zpow _ _ _).trans (congrArg (· ^ (n : ℤ))
      ((gm_res (𝟙 Y) y (le j) hy _).trans (gm_pull (𝟙 Y) ψ y (((PP L p N).pull F).U (fun _ _ => j 0) ⊓ (PP L p N).U (fun _ => j 1)) (le j hy) _)))
  refine ⟨α, isGen_of_gm α fun y j j' hj hj' => ?_, hα⟩
  have e := (isGen_iff w).1 hw Y ψ y _ _ _ _ (h0 j y hj) (h0 j' y hj') (h1 j y hj) (h1 j' y hj')
  have e0 := gm_linComb L (fun _ : Fin 1 => p) (fun _ => (N : ℤ)) (ψ ≫ F) y (fun _ => j 0) (fun _ => j' 0)
    (h0 j y hj) (h0 j' y hj')
  have e1 := gm_linComb L (fun _ : Fin 1 => p) (fun _ => (N : ℤ)) ψ y (fun _ => j 1) (fun _ => j' 1)
    (h1 j y hj) (h1 j' y hj')
  rw [Fin.prod_univ_one] at e0 e1
  have e' := e.trans (congrArg₂ (fun a b => a * b⁻¹ * _) e0 e1)
  rw [hα j y hj, hα j' y hj', e', trF, Fin.prod_univ_two, hψ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp, mul_zpow, inv_zpow, ← zpow_mul,
    Nat.cast_mul, zpow_neg]

theorem chart_le {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => p) j ≤ LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

def rho {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) :
    Γ(Y, LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j)) →+* Γ(Y, LB.wchart L (fun _ : Fin 1 => p) j) :=
  (Y.presheaf.map (homOfLE (chart_le L p N j)).op).hom

theorem rho_injective {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) :
    Function.Injective (rho L p N j) := fun a b h => fn_ext fun y hy => by
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : Fin 1 => p) j := Set.mem_iInter.1 hy 0
  exact (gs_res (𝟙 Y) y (chart_le L p N j) hy' a).symm.trans ((congrArg (gs (𝟙 Y) y _) h).trans
    (gs_res (𝟙 Y) y (chart_le L p N j) hy' b))

theorem rho_resTop {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) (c : Γ(Y, ⊤)) :
    rho L p N j (resTop _ c) = resTop _ c := fn_ext fun y hy =>
  (gs_res (𝟙 Y) y (chart_le L p N j) hy _).trans ((gs_res (𝟙 Y) y le_top (chart_le L p N j hy) c).trans
    (gs_res (𝟙 Y) y le_top hy c).symm)

theorem exists_iso {K : Type} [CommRing K] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (Y : Over (Spec (CommRingCat.of K))) [IsProper Y.hom] (p : Y.left ⟶ X) (N : ℕ) (hA : RelAmple Y (PP L p N))
    (Φ : ∀ n : ℕ, 1 ≤ n → LB.Sec (PP L p ((N * n : ℕ) : ℤ)) ≃ LB.Sec (PP L p ((N * n : ℕ) : ℤ)))
    (hlin : ∀ n hn (c : K) (s s' s'' : LB.Sec (PP L p ((N * n : ℕ) : ℤ))),
      (∀ j, s''.f j = resTop _ (scal Y.hom c) * s.f j + s'.f j) →
      ∀ j, (Φ n hn s'').f j = resTop _ (scal Y.hom c) * (Φ n hn s).f j + (Φ n hn s').f j)
    (hmul : ∀ n m hn hm hnm (s : LB.Sec (PP L p ((N * n : ℕ) : ℤ))) (s' : LB.Sec (PP L p ((N * m : ℕ) : ℤ)))
      (s'' : LB.Sec (PP L p ((N * (n + m) : ℕ) : ℤ))),
      (∀ j, @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) (s''.f j) =
        @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) (s.f j) *
          @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) (s'.f j)) →
      ∀ j, @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ (n + m) hnm s'').f j) =
        @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ n hn s).f j) *
          @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ m hm s').f j)) :
    ∃ ψ : Y ≅ Y, ∀ (m : Y.left ⟶ X), ψ.hom.left ≫ p = m → ∀ n hn,
      ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![p, m] ![((N * n : ℕ) : ℤ), -((N * n : ℕ) : ℤ)]), α.IsGen ∧
        ∀ s (j : Fin 2 → L.ι) (y : Y.left), y ∈ LB.wchart L ![p, m] j →
          gs (𝟙 _) y (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 0)) ((Φ n hn s).f (fun _ => j 0)) =
            (gm (𝟙 _) y (LB.wchart L ![p, m] j) (α.s j)).val *
              gs ψ.hom.left y (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 1)) (s.f (fun _ => j 1)) := by
  choose E hE using fun n => exists_equiv L p N n
  have hE' : ∀ n a j, @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((E n a).f j) =
      rho L p N j (a.f (fun _ => j)) := fun n a j =>
    fn_ext fun y hy => (hE n a j _ (𝟙 _) y hy).trans (gs_res (𝟙 _) y (chart_le L p N j) hy _).symm
  let θ : ∀ n : ℕ, 1 ≤ n → (H0 (PP L p N) n ≃ H0 (PP L p N) n) := fun n hn => (E n).trans ((Φ n hn).trans (E n).symm)
  have hθE : ∀ n hn a, E n (θ n hn a) = Φ n hn (E n a) := fun n hn a => (E n).apply_symm_apply _
  have hθ : ∀ n hn a j, rho L p N j ((θ n hn a).f (fun _ => j)) =
      @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ n hn (E n a)).f j) := fun n hn a j => by
    rw [← hE', hθE]
  have one : ∀ j : Fin 1 → (PP L p N).ι, ∃ i, j = fun _ => i := fun j =>
    ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
  obtain ⟨Φ₀, w, hw, H⟩ := exists_iso_of_sectionRing_aut_of_relAmple K Y (PP L p N) (LB.isLB_linComb hL _ _) hA θ
    (fun n hn c a b d h j => by
      obtain ⟨i, rfl⟩ := one j
      apply rho_injective L p N i
      have e := hlin n hn c (E n b) (E n a) (E n d) (fun j => (hE' n d j).trans ((congrArg (rho L p N j) (h _)).trans
        ((map_add _ _ _).trans ((add_comm _ _).trans (congrArg₂ (· + ·) ((map_mul _ _ _).trans
          (congrArg₂ (· * ·) (rho_resTop L p N j _) (hE' n b j).symm)) (hE' n a j).symm))))) i
      exact (hθ n hn d i).trans (e.trans ((map_add _ _ _).trans ((add_comm _ _).trans (congrArg₂ (· + ·)
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) (rho_resTop L p N i _) (hθ n hn b i))) (hθ n hn a i)))).symm))
    (fun n m hn hm a b d h j => by
      obtain ⟨i, rfl⟩ := one j
      apply rho_injective L p N i
      have e := hmul n m hn hm (hn.trans (Nat.le_add_right n m)) (E n a) (E m b) (E (n + m) d)
        (fun j => (hE' _ d j).trans ((congrArg (rho L p N j) (h _)).trans
          ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hE' n a j).symm (hE' m b j).symm)))) i
      exact (hθ _ _ d i).trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hθ n hn a i) (hθ m hm b i))).symm))
  have hψ : Φ₀.inv.left ≫ Φ₀.hom.left = 𝟙 _ := by rw [← Over.comp_left, Φ₀.inv_hom_id, Over.id_left]
  refine ⟨Φ₀.symm, fun m hm n hn => ?_⟩
  obtain ⟨α, hα, hv⟩ := exists_gen_of_iso L p N n Φ₀.hom.left Φ₀.inv.left hψ m hm w hw
  refine ⟨α, hα, fun s j y hy => ?_⟩
  obtain ⟨a, rfl⟩ := (E n).surjective s
  have hF : Φ₀.hom.left (Φ₀.inv.left y) = y := by
    rw [← Scheme.Hom.comp_apply, hψ]; rfl
  have h0 : y ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 0) := mem_one.2 (Set.mem_iInter.1 hy 0)
  have h1 : Φ₀.inv.left y ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 1) := by
    subst hm; exact mem_one.2 (Set.mem_iInter.1 hy 1)
  have e := H n hn a _ Φ₀.inv.left y (fun _ _ => j 0) (fun _ _ => j 1)
    (fun _ => (congrArg (· ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 0)) hF).mpr h0) (fun _ => h1)
  rw [hψ, Fin.prod_univ_one, Category.comp_id] at e
  rw [← hθE, hE n _ _ _ (𝟙 _) y h0, hv j y hy]
  exact e.trans (congrArg _ (hE n a _ _ Φ₀.inv.left y h1).symm)

end SectionAut

theorem exists_iso_of_multiplicative_section_family : ∀ (F : Type) [Field F] (S : Scheme.{0}) (P : PolAV S) (t : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), 1 ≤ N → ∀ Φ : ∀ k : ℕ, LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)) ≃ LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)), (∀ k (s s' s'' : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (c : Γ((Over.mk t).left, ⊤)), (∀ j, s''.f j = liftFun P.A _ c * s.f j + s'.f j) → ∀ j, (Φ k s'').f j = liftFun P.A _ c * (Φ k s).f j + (Φ k s').f j) → (∀ k l (s : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (s' : LB.Sec (LPow P.A P.L ((N * (l + 1) : ℕ) : ℤ) (Over.mk t))) (s'' : LB.Sec (LPow P.A P.L ((N * (k + l + 1 + 1) : ℕ) : ℤ) (Over.mk t))), (∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s''.f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s.f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s'.f j)) → ∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ (k + l + 1) s'').f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ k s).f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ l s').f j)) → ∃ (ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P.A) (_ : ψ.hom ≫ fst _ _ = fst _ _), ∀ k, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk t) P.A).left, (ψ.hom ≫ snd _ _).left] ![((N * (k + 1) : ℕ) : ℤ), -((N * (k + 1) : ℕ) : ℤ)]), α.IsGen ∧ ∀ s, IsTwistPull P.A P.L ψ.hom (ψ.hom ≫ snd _ _) rfl _ _ α s (Φ k s) := by
  intro F _ S P t N hN Φ hlin hmul
  obtain ⟨hp, hA⟩ := isProper_and_relAmple_lPow F S P t N hN
  have hp' : IsProper (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left).hom := hp
  have hmul' : ∀ k l m (_ : m = k + l + 1) (s : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)))
      (s' : LB.Sec (LPow P.A P.L ((N * (l + 1) : ℕ) : ℤ) (Over.mk t)))
      (s'' : LB.Sec (LPow P.A P.L ((N * (m + 1) : ℕ) : ℤ) (Over.mk t))),
      (∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s''.f j) =
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s.f j) *
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s'.f j)) →
      ∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ m s'').f j) =
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ k s).f j) *
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ l s').f j) := by
    rintro k l _ rfl
    exact hmul k l
  obtain ⟨ψ₀, H⟩ := SectionAut.exists_iso P.L P.isLB
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) (snd (Over.mk t) P.A).left N hA
    (fun n hn => match n, hn with | k + 1, _ => Φ k)
    (fun n hn c => match n, hn with
      | k + 1, _ => fun s s' s'' => hlin k s s' s'' ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c))
    (fun n m hn hm _ => match n, m, hn, hm with
      | k + 1, l + 1, _, _ => hmul' k l (k + 1 + l) (by omega))
  have w₀ : ψ₀.hom.left ≫ (fst (Over.mk t) P.A).left = (fst (Over.mk t) P.A).left := Over.w ψ₀.hom
  let ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P.A := Over.isoMk ((Over.forget _).mapIso ψ₀) (by
    have e : (fst (Over.mk t) P.A).left ≫ t = (Over.mk t ⊗ P.A).hom := Over.w (fst (Over.mk t) P.A)
    show ψ₀.hom.left ≫ (Over.mk t ⊗ P.A).hom = (Over.mk t ⊗ P.A).hom
    rw [← e, ← Category.assoc, w₀])
  refine ⟨ψ, Over.OverMorphism.ext w₀, fun k => ?_⟩
  obtain ⟨α, hα, hv⟩ := H (ψ.hom ≫ snd _ _).left rfl (k + 1) (Nat.succ_pos k)
  refine ⟨α, hα, fun s j => fn_ext fun y hy => ?_⟩
  have l₀ := chart_le_zero P.A P.L (ψ.hom ≫ snd _ _) j
  have l₁ := chart_le_pull P.A P.L ψ.hom (ψ.hom ≫ snd _ _) rfl j
  exact (gs_res (𝟙 _) y l₀ hy _).trans ((hv s j y hy).trans ((gs_mul (𝟙 _) y _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) ((gs_res (𝟙 _) y l₁ hy _).trans
      (gs_pull (𝟙 _) ψ.hom.left y
        (LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) (fun _ => j 1)) (l₁ hy) _)))).symm)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericPol

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_lift {K : Type} [Field K] {X Z : Scheme.{0}} (x : Spec (CommRingCat.of K) ⟶ X) (j : Z ⟶ X)
    (h : Set.range x ⊆ Set.range j) :
    ∃ (K' : Type) (_ : Field K') (i : K →+* K') (z : Spec (CommRingCat.of K') ⟶ Z), specOf i ≫ x = z ≫ j := by
  obtain ⟨z, hz⟩ := h ⟨(default : PrimeSpectrum K), rfl⟩
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := j) _ z hz.symm
  let u := (pullback x j).fromSpecResidueField p
  refine ⟨(pullback x j).residueField p, inferInstance, (Spec.preimage (u ≫ pullback.fst x j)).hom,
    u ≫ pullback.snd x j, ?_⟩
  have e : specOf (Spec.preimage (u ≫ pullback.fst x j)).hom = u ≫ pullback.fst x j :=
    Spec.map_preimage _
  rw [e]
  exact (Category.assoc _ _ _).trans ((congrArg (u ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Host E}

theorem proper_ample_kTriv {X Z : Scheme.{0}} {T : SAB H X} {T' : SAB H Z} {j : Z ⟶ X} (mj : SABMap T' T j)
    (hp : IsProper T'.G.hom) (hA : RelAmple T'.G T'.PP.L) (hK : KTriv T'.G T'.PP.L) {K : Type} [Field K]
    {x : Spec (CommRingCat.of K) ⟶ X} {t : SAB H (Spec (CommRingCat.of K))} (m : SABMap t T x)
    (h : Set.range x ⊆ Set.range j) : IsProper t.G.hom ∧ RelAmple t.G t.PP.L ∧ KTriv t.G t.PP.L := by
  obtain ⟨K', _, i, z, e⟩ := exists_lift x j h
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull CubePf.cubePull (specOf i) t
  generalize (⟨(Over.pullback (specOf i)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t' at m₁
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ T T' t' j z mj (e ▸ n)
  obtain ⟨w, g, -⟩ := m'.lin
  obtain ⟨w₁, g₁, -⟩ := m₁.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K')) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hc)).mpr trivial
  have := t.semi.smooth
  have := t.semi.separated
  have := t.semi.quasiCompact
  exact GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension K K' i t.G t'.G m₁.φ m₁.cart t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ⟨w₁, g₁⟩
    (MorphismProperty.of_isPullback (P := @IsProper) m'.cart.1 hp)
    (relAmple_pull m'.cart.1 T'.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) U hU hy hA)
    (kTriv_pull m'.cart T'.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) hK)

def toPolAV {S : Scheme.{0}} (t : SAB H S) (g : ℕ) (hg : SmoothOfRelativeDimension g t.G.hom) (hp : IsProper t.G.hom)
    (hA : RelAmple t.G t.PP.L) (hK : KTriv t.G t.PP.L) : PolAV S where
  A := t.G
  isAb := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  g := g
  smoothDim := hg
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := by
    obtain ⟨-, w, hw, -⟩ := t.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  ample := hA
  ktriv := hK

theorem rosatiAdj {S : Scheme.{0}} (t : SAB H S) (a : NumberField.RingOfIntegers E) :
    RosatiAdj t.G t.PP.L (t.act.act a) (t.act.act (H.bar a)) := by
  obtain ⟨u, hu⟩ := GlobalTheory.NormRos.exists_gen_rosati t.PP.isLB _ _ (t.adj a)
  exact fun _ => ⟨⊤, trivial, LB.pullGen _ _ _ u _, DVR.pullGen_isGen _ _ _ _ hu _⟩

end GlobalTheory.GenericPol


open GlobalTheory.GenericPol ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem GlobalTheory.exists_polAV_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (Dm : Geo.Tor.Datum H) (l : Geo.Tor.Level H) (Xo : Geo.Tor.Moduli Dm l) (c : Geo.Tor.Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Geo.Tor.Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (χ : Geo.Tor.Sp R ⟶ Y.X) (t : Geo.Tor.SAB H (Geo.Tor.Sp R)) (_ : Geo.Tor.SABMap t Y.t χ), Set.range (jK R ≫ χ) ⊆ Set.range Y.j → ∀ g : ℕ, SmoothOfRelativeDimension g t.G.hom → ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (eA : (Over.pullback (jK R)).obj t.G ≅ A.A) (oA : letI := H.starRing; A.OAct (NumberField.RingOfIntegers E)), A.g = g ∧ IsMonHom eA.hom ∧ Geo.Tor.LBIso (A.L.pull eA.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) ∧ (letI := H.starRing; ∀ a, (Over.pullback (jK R)).map (t.act.act a) ≫ eA.hom = eA.hom ≫ oA.act a) := by
  intro E _ _ _ H Dm l Xo c O _ β Y R _ _ χ t m h g hg
  let := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (jK R) t
  let t' : SAB H (Spec (CommRingCat.of (FractionRing R))) :=
    ⟨(Over.pullback (jK R)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
      Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (jK R) := m₁
  have hm₀ : m₀.cm.F = pullback.fst t.G.hom (jK R) := hm₁
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₀
  obtain ⟨hp, hA, hK⟩ := proper_ample_kTriv Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv n h
  have hg' : SmoothOfRelativeDimension g t'.G.hom := by
    show SmoothOfRelativeDimension g (pullback.snd t.G.hom (jK R))
    exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨w, hw, -⟩ := m₀.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := hm₀ ▸ ⟨w, hw⟩
  refine ⟨toPolAV t' g hg' hp hA hK, Iso.refl _, ⟨t'.act.toRingAct, rosatiAdj t'⟩, rfl, ?_, ?_, fun a => ?_⟩
  · exact inferInstanceAs (IsMonHom (𝟙 t'.G))
  · exact LBIso.chartPull (Geo.Tor.chartPullPull t'.PP.L (𝟙 _) (𝟙 _) rfl) (Geo.Tor.chartPullId _) hL
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecZeroOfPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.SchurConst

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split_ifs with h
  · simp only [map_zero]
  · rfl

theorem sec_zero_of_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0)
    (j : K → L.ι) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans (gs_zero _ _ _).symm

theorem sec_zero_of_pull {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K₃ : Type} [Fintype K] [Fintype K₃]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (τ : Y' ⟶ Y) (σ : Y ⟶ Y') (hστ : σ ≫ τ = 𝟙 Y)
    {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (h : ∀ y J, Good L y J → sval s τ y J = 0) (j : K → L.ι) : s.f j = 0 := by
  have h1 := sec_zero_of_val hL (pullMulSec s τ u hu) (fun y J hJ => by
    rw [sval_pullMulSec s τ u hu _ y hJ, Category.id_comp, h y J hJ, zero_mul])
  refine sec_zero_of_val hL s (fun y J hJ => ?_) j
  have h2 : sval (pullMulSec s τ u hu) σ y J = 0 := by
    unfold sval
    rw [h1]
    exact gs_zero _ _ _
  rw [sval_pullMulSec s τ u hu _ y hJ, hστ] at h2
  exact (Units.mul_left_eq_zero _).1 h2

theorem main : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → (∀ α, ∃ t s, U.ExpF (Kbar V) N t s ∧ DegPre.FamFE D (Kbar V) N s ∧ ∃ j, (s α).f j ≠ 0) → U.FE (Kbar V) N := by
  intro hL1 hL2 V _ _ _ hV D A G _ _ U N hN hw t s hts mu α u hu hcorr
  obtain ⟨t₀, s₀, he₀, hfe₀, j, hj⟩ := hw α
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.UU.SchurComp.components_proportional hL1 hL2 V hV D A G U N hN α mu u hu ⟨t₀, s₀, he₀, j, hj⟩
  have hc : ∀ (z : (DegPre.BF D (Kbar V)).left) (b c : Kbar V),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (b * c) ⊤) =
        gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) b ⊤) * gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) c ⊤) := by
    intro z b c
    rw [← gs_mul _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_mul]
  have hc1 : ∀ (z : (DegPre.BF D (Kbar V)).left),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) 1 ⊤) = 1 := by
    intro z
    rw [gs_eq _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_one]
  have hca : ∀ (z : (DegPre.BF D (Kbar V)).left) (b : Kbar V),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (b - 1) ⊤) =
        gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) b ⊤) - 1 := by
    intro z b
    rw [gs_eq _ _ ⊤ trivial, gs_eq _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_sub, map_one]
  have ha1 : a = 1 := by
    by_contra hne
    apply hj
    have hinv : (DegPre.trF D (Kbar V) (-mu)).left ≫ (DegPre.trF D (Kbar V) mu).left = 𝟙 _ := by
      rw [← Over.comp_left, DVR.UUA.trF_add, neg_add_cancel, DVR.UUA.trF_zero, Over.id_left]
    refine sec_zero_of_pull D.P.isLB (s₀ α) _ _ hinv u hu (fun z J hJ => ?_) j
    have e1 := ha t₀ s₀ he₀ z J hJ
    have e2 := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).1 (hfe₀ mu α u hu hcorr) _ (𝟙 _) z J hJ
    rw [Category.id_comp] at e2
    have e3 : gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (a - 1) ⊤) *
        (sval (s₀ α) (DegPre.trF D (Kbar V) mu).left z J * (val u (𝟙 _) z J).val) = 0 := by
      rw [hca, _root_.sub_mul, _root_.one_mul, ← e1, ← e2, sub_self]
    have e4 := congrArg (gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (a - 1)⁻¹ ⊤) * ·) e3
    simp only [mul_zero] at e4
    rw [← _root_.mul_assoc, ← hc, inv_mul_cancel₀ (sub_ne_zero.2 hne), hc1, _root_.one_mul] at e4
    exact (Units.mul_left_eq_zero _).1 e4
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).2 fun z J hJ => ?_
  rw [Category.id_comp, ha t s hts z J hJ, ha1, hc1, _root_.one_mul]

end GlobalTheory.UU.SchurConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSectionSupportEqUniv
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU

theorem theta_support_eq_univ : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∀ α, ∃ j, (f α).f j ≠ 0) ∧ ∀ α, U.Supp (Kbar V) 2 α) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U θ f hθ
  have hrel := _root_.GlobalTheory.UU.SuppRel.supp_rel h1 h2 V hV D A G U θ f hθ
  have hodd := _root_.GlobalTheory.UU.PrimeIndex.hom_zmod_eq_zero_of_support h1 h2 V hV D A G U θ f hθ
  have hw := _root_.GlobalTheory.UU.Weight.main h1 h2 V hV D A G U
  have hpull := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hpull.1 θ
  obtain ⟨s₀, hs₀, -⟩ := hpull.2 f
  have hone := (GlobalTheory.T.expF_of_theta_degree_one h1 h2 V hV D A G U θ f hθ th s₀ hth hs₀).2.2
  have hne : ({α | ∃ j, (f α).f j ≠ 0} : Set D.X).Nonempty := by
    obtain ⟨mu, t, s, hts, j, hj⟩ := (hw 1 le_rfl).2.1 0
    obtain ⟨c, hc⟩ := hone t s hts
    refine ⟨0 + 1 • mu, (_root_.GlobalTheory.pullB_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ _).1 ⟨j, fun h0 => hj ?_⟩⟩
    rw [hc, h0, mul_zero]
  obtain ⟨hS, Λ, hΛ, hc⟩ := GlobalTheory.support_subgroup_odd_index D.X {α | ∃ j, (f α).f j ≠ 0}
    {α | U.Supp (Kbar V) 2 α} hne hrel (fun x => by
      obtain ⟨mu, hmu⟩ := (hw 2 (by norm_num)).2.1 x
      exact ⟨mu, by rw [← two_nsmul]; exact hmu⟩)
  have htop : Λ = ⊤ := by
    rcases hc with h | ⟨l, hl, -, g, hg, hgΛ⟩
    · exact h
    · refine absurd (hodd l hl g fun α hα => hgΛ α ?_) hg
      have : α ∈ (Λ : Set D.X) := by rw [hΛ]; exact hα
      exact this
  have hall : ∀ α, α ∈ ({α | ∃ j, (f α).f j ≠ 0} : Set D.X) := fun α => by
    rw [← hΛ, htop]; trivial
  refine ⟨hall, fun α => ?_⟩
  have : α ∈ ({α | U.Supp (Kbar V) 2 α} : Set D.X) := by rw [hS]; exact hall α
  exact this

end GlobalTheory.UU
end

