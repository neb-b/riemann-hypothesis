module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ChangeChart
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvenAlong
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

variable {B B' G G' T T' S S₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {p : T ⟶ B} {p' : T' ⟶ B'} {f : T ⟶ G} {f' : T' ⟶ G'}

theorem rig_box (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    (hwe : we.IsGen) (Q : BoxSquare w we we' h)
    (hF : ∀ i, h i ≫ f = f' ≫ prG i) (hE : ∀ i, p' ≫ pr i = h i ≫ p)
    {u : S ⟶ T} {u' : S ⟶ T'} {s : S ⟶ S₀} {eG : S₀ ⟶ G} {eA : S₀ ⟶ B} {eG' : S₀ ⟶ G'} {eA' : S₀ ⟶ B'}
    {rL : LB.Gen (L.pull eG)} (hrL : rL.IsGen) {rM : LB.Gen (M.pull eA)} {rM' : LB.Gen (M'.pull eA')}
    (H : RigAlong we u s rL rM) (hu : ∀ i, u' ≫ h i = u) (hf : u ≫ f = s ≫ eG) (hp : u ≫ p = s ≫ eA)
    (hp' : u' ≫ p' = s ≫ eA') (hG : ∀ (i : Fin j) (_ : PUnit), eG' ≫ prG i = 𝟙 S₀ ≫ eG)
    (b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => eA' ≫ pr i) (fun _ => 1)))
    (b₁ : GeneratorPullback.MapsAt M M' pr w eA' 1 rM' b)
    (b₂ : LB.Gen.Corr M _ _ _ _ b (GeneratorPullback.finProdGen M (J := Fin j) (fun _ _ => eA) (fun _ _ => 1) (fun _ => rM))) :
    RigAlong we' u' s (GeneratorPullback.boxGen L prG (fun _ : PUnit => eG') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (prG i) (𝟙 S₀) (fun _ => eG) (fun _ => 1) (fun _ => eG') (hG i) rL)) rM' := by
  rintro ⟨qM, qL⟩ V a₁ a₂ a₃
  refine unit_ext fun y hy => ?_
  have key := rel_box hM hM' hL hwe Q hF hE (K := PUnit) (ε := fun _ => 1) y (fun _ => u') hrL rM rM' s
    (fun _ => s) (fun _ => s) (fun i _ => by rw [hu, hf]) (fun _ => hp') (fun i _ => by rw [hu, hp])
    (fun J J' hJ hJ' => (congrArg₂ (· * ·) (Fintype.prod_unique _) rfl).trans
      ((mapsAt_val w eA' 1 rM' b b₁ s y hJ hJ').symm.trans ((val_corr hJ b₂ s).trans (val_finProd _ _ _ s y hJ))))
    (fun i J N hJ hN => by
      have e := H.stalk hf hp (𝟙 S) y (J (s ≫ eA)) (N (s ≫ eG)) ((pt_of_eq hp y).symm ▸ hJ (s ≫ eA))
        ((pt_of_eq hf y).symm ▸ hN (s ≫ eG))
      rw [Category.id_comp, Category.id_comp] at e
      rw [Fintype.prod_unique, zpow_one, hu]
      exact e.symm)
    qL qM (fun a b _ => congrArg qM (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 (a₃ hy) k)
    (fun k i => (pt_of_eq (hG i k) (s y)) ▸ Set.mem_iInter.1 (Set.mem_iInter.1 (a₂ hy) k) i)
  rw [Fintype.prod_unique, zpow_one] at key
  have e := gm_box_pull L prG (fun _ => 𝟙 S₀) hG (fun _ => rL) s y qL (a₂ hy)
  rw [Category.comp_id] at e
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res_pull _ u' y a₁ hy _)
    (gm_res_pull _ s y a₂ hy _)).trans (Eq.trans ?_ (gm_res_pull _ s y a₃ hy _).symm))
  rw [Category.id_comp, Category.id_comp]
  exact (congrArg₂ (· * ·) rfl e).trans key.symm

def EvenAlong (we : LB.Iso (L.pull f) (M.pull p)) (iT : T ⟶ T) {iG : G ⟶ G} {iB : B ⟶ B}
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]))
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])) : Prop :=
  ∀ (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι),
    LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS →
    LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT →
    ∀ (V : T.Opens) (h₁ : V ≤ p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT)
      (h₂ : V ≤ (M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1))
      (h₃ : V ≤ iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)))
      (h₄ : V ≤ f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS),
      res h₁ (pullU p _ (σ.s jT)) * res h₂ (we.s (fun _ => jT 1, fun _ => jS 1)) =
        res h₃ (pullU iT _ (we.s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU f _ (s.s jS))

theorem EvenAlong.stalk {we : LB.Iso (L.pull f) (M.pull p)} {iT : T ⟶ T} {iG : G ⟶ G} {iB : B ⟶ B}
    {s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1])}
    {σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])} (ev : EvenAlong we iT s σ)
    (iF : iT ≫ f = f ≫ iG) (iP : iT ≫ p = p ≫ iB) {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z)
    (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι) (cS : LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS)
    (cT : LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT)
    (hS : ∀ k, (![iG, 𝟙 G] : Fin 2 → (G ⟶ G)) k (f (r z)) ∈ L.U (jS k))
    (hT : ∀ k, (![iB, 𝟙 B] : Fin 2 → (B ⟶ B)) k (p (r z)) ∈ M.U (jT k)) :
    gm (r ≫ p) z (LB.wchart M (K := Fin 2) ![iB, 𝟙 B] jT) (σ.s jT) =
      (∏ k, Geo.Tor.gw we ((![r ≫ iT, r] : Fin 2 → _) k) z (jT k) (fun _ => jS k) ^ (![1, -1] : Fin 2 → ℤ) k) *
        gm (r ≫ f) z (LB.wchart L (K := Fin 2) ![iG, 𝟙 G] jS) (s.s jS) := by
  have S0 : f (iT (r z)) ∈ L.U (jS 0) := (pt_of_eq iF (r z)).symm ▸ hS 0
  have T0 : p (iT (r z)) ∈ M.U (jT 0) := (pt_of_eq iP (r z)).symm ▸ hT 0
  have S1 : f (r z) ∈ L.U (jS 1) := hS 1
  have T1 : p (r z) ∈ M.U (jT 1) := hT 1
  let W : T.Opens := p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT ⊓
    ((M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1)) ⊓
    iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)) ⊓
    f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS
  have hW : r z ∈ W := ⟨⟨⟨Set.mem_iInter.2 hT, mem_pull.2 T1, mem_pull.2 S1⟩, mem_pull.2 T0, mem_pull.2 S0⟩,
    Set.mem_iInter.2 hS⟩
  have l₁ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have l₂ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have l₃ : W ≤ _ := inf_le_left.trans inf_le_right
  have l₄ : W ≤ _ := inf_le_right
  obtain ⟨n₁, n₂⟩ := GlobalTheory.EvenPull.even_stalk we s σ jS jT W l₁ l₂ l₃ l₄ r z hW
  have E := n₁.symm.trans ((congrArg (gm r z W) (ev jS jT cS cT W l₁ l₂ l₃ l₄)).trans n₂)
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg]
  rw [← mul_right_comm, ← E, mul_inv_cancel_right]

theorem even_box (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    (hwe : we.IsGen) (Q : BoxSquare w we we' h)
    (hF : ∀ i, h i ≫ f = f' ≫ prG i) (hE : ∀ i, p' ≫ pr i = h i ≫ p)
    {iT : T ⟶ T} {iG : G ⟶ G} {iB : B ⟶ B} {iT' : T' ⟶ T'} {iG' : G' ⟶ G'} {iB' : B' ⟶ B'}
    (ih : ∀ i, iT' ≫ h i = h i ≫ iT) (iF : iT ≫ f = f ≫ iG) (iP : iT ≫ p = p ≫ iB) (iP' : iT' ≫ p' = p' ≫ iB')
    (hG : ∀ i k, (![iG', 𝟙 G'] : Fin 2 → _) k ≫ prG i = prG i ≫ (![iG, 𝟙 G] : Fin 2 → _) k)
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1])) (hs : s.IsGen)
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]))
    (σ' : LB.Gen (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]))
    (hσ : ∀ (y : T') J J', Good M y J → Good M' y J' →
      om w y J J' (p' ≫ iB') * (om w y J J' p')⁻¹ * val σ' p' y J' = ∏ i, val σ (p' ≫ pr i) y J)
    (ev : EvenAlong we iT s σ) :
    EvenAlong we' iT' (GeneratorPullback.boxGen L prG _ _ (fun i => GeneratorPullback.pullAlong L (prG i) (prG i) _ _ _ (hG i) s)) σ' := by
  intro jS' jT' _ cT V h₁ h₂ h₃ h₄
  refine unit_ext fun z hz => ?_
  obtain ⟨k₁, k₂⟩ := GlobalTheory.EvenPull.even_stalk we'
    (GeneratorPullback.boxGen L prG _ _ (fun i => GeneratorPullback.pullAlong L (prG i) (prG i) _ _ _ (hG i) s)) σ' jS' jT' V h₁ h₂ h₃ h₄
    (𝟙 T') z hz
  refine k₁.trans (Eq.trans ?_ k₂.symm)
  clear k₁ k₂
  have c₀ : ∀ i k, (![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i = (![h i ≫ iT, h i] : Fin 2 → _) k :=
    fun i => Fin.forall_fin_two.2 ⟨ih i, Category.id_comp _⟩
  have c₁ : ∀ i k, ((![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i) ≫ f = (h i ≫ f) ≫ (![iG, 𝟙 G] : Fin 2 → _) k :=
    fun i => Fin.forall_fin_two.2 ⟨by
      show (iT' ≫ h i) ≫ f = (h i ≫ f) ≫ iG
      rw [ih, Category.assoc, iF, Category.assoc], by
      show (𝟙 T' ≫ h i) ≫ f = (h i ≫ f) ≫ 𝟙 G
      rw [Category.id_comp, Category.comp_id]⟩
  have c₃ : ∀ i k, ((![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i) ≫ p = (h i ≫ p) ≫ (![iB, 𝟙 B] : Fin 2 → _) k :=
    fun i => Fin.forall_fin_two.2 ⟨by
      show (iT' ≫ h i) ≫ p = (h i ≫ p) ≫ iB
      rw [ih, Category.assoc, iP, Category.assoc], by
      show (𝟙 T' ≫ h i) ≫ p = (h i ≫ p) ≫ 𝟙 B
      rw [Category.id_comp, Category.comp_id]⟩
  have mL : ∀ k i, (![iG, 𝟙 G] : Fin 2 → (G ⟶ G)) k ((h i ≫ f) z) ∈ L.U (jS' k i) := fun k i => by
    have a : ((f' ≫ (![iG', 𝟙 G'] : Fin 2 → (G' ⟶ G')) k) ≫ prG i) z ∈ L.U (jS' k i) :=
      Set.mem_iInter.1 (Set.mem_iInter.1 (h₄ hz) k) i
    rw [Category.assoc, hG, ← Category.assoc, ← hF] at a
    exact a
  have HM : ∀ J J', Good M z J → Good M' z J' →
      (∏ k, om w z J J' (p' ≫ (![iB', 𝟙 B'] : Fin 2 → _) k) ^ (![1, -1] : Fin 2 → ℤ) k) * val σ' p' z J' =
        ∏ i, val σ (h i ≫ p) z J := fun J J' hJ hJ' => by
    have e := hσ z J J' hJ hJ'
    simp only [hE] at e
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, zpow_one, zpow_neg]
    exact e
  have HU : ∀ i J N, Good M z J → Good L z N → val σ (h i ≫ p) z J =
      (∏ k, Geo.Tor.gw we ((![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i) z (J ((h i ≫ p) ≫ (![iB, 𝟙 B] : Fin 2 → _) k))
        (fun _ => N ((h i ≫ f) ≫ (![iG, 𝟙 G] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) * val s (h i ≫ f) z N :=
    fun i J N hJ hN => by
      simp only [c₀]
      exact ev.stalk iF iP (h i) z _ _
        (fun a b e => congrArg N ((Category.assoc _ _ _).trans ((congrArg (h i ≫ ·) e).trans
          (Category.assoc _ _ _).symm)))
        (fun a b e => congrArg J ((Category.assoc _ _ _).trans ((congrArg (h i ≫ ·) e).trans
          (Category.assoc _ _ _).symm)))
        (fun k => hN ((h i ≫ f) ≫ (![iG, 𝟙 G] : Fin 2 → _) k)) (fun k => hJ ((h i ≫ p) ≫ (![iB, 𝟙 B] : Fin 2 → _) k))
  have key := rel_box hM hM' hL hwe Q hF hE (K := Fin 2) (ε := ![1, -1]) z ![iT', 𝟙 T'] hs σ σ' p'
    (fun i => h i ≫ p) (fun i => h i ≫ f) c₁
    (Fin.forall_fin_two.2 ⟨iP', (Category.id_comp _).trans (Category.comp_id _).symm⟩) c₃ HM HU
    jS' jT' cT (fun k => Set.mem_iInter.1 (h₁ hz) k) mL
  have e := gm_box_pull L prG prG hG (fun _ => s) f' z jS' (h₄ hz)
  rw [Fin.prod_univ_two] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, hF] at key
  rw [Category.id_comp, Category.id_comp, Category.id_comp]
  refine Eq.trans ?_ (congrArg₂ (· * ·) rfl e).symm
  rw [key, mul_right_comm, inv_mul_cancel_right]

end GlobalTheory.PowUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace ExpansionValueZero

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cst_comp {A C : Type} [CommRing A] [CommRing C] {Z : Scheme.{0}} (q : Z ⟶ Sp C) (φ : A →+* C) (z : Z) (a : A) :
    cst (q ≫ spMap φ) z a = cst q z (φ a) := by
  rw [← H1.cst_stalkMap, H1.gs_spec, H1.cst_stalkMap, Category.comp_id]

theorem cst_sum {A : Type} [CommRing A] {Z : Scheme.{0}} (q : Z ⟶ Sp A) (z : Z) {K : Type} (S : Finset K) (a : K → A) :
    cst q z (∑ i ∈ S, a i) = ∑ i ∈ S, cst q z (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cst, gs_eq q z ⊤ trivial, map_sum]

theorem exists_coeff {A : Type} [CommRing A] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp A ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (e : Sp A ⟶ Y) (t : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen)
    (h : FormEq (fun k => e ≫ φ k) ε φ' ε') :
    ∃ a : A, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp A) (z : Z) (J), Good L z J →
      sval s (r ≫ e) z J = cst r z a * (val t r z J).val := by
  obtain ⟨s', hv⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [h U f, mul_inv_cancel])
    (pullMulSec s e (LB.invGen L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
  have le : (⊤ : (Sp A).Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Sp A ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
    (((Sp A).presheaf.map (homOfLE le).op).hom (s'.f PEmpty.elim))
  refine ⟨a, fun Z r z J hJ => ?_⟩
  have e₁ := hv Z r z J hJ
  rw [sval_pullMulSec _ _ _ _ _ _ hJ, val_inv, sval_of s' r z J PEmpty.elim (fun k => k.elim)] at e₁
  have e₂ : cst r z a = sval s (r ≫ e) z J * ((val t r z J)⁻¹).val :=
    (congrArg (gs r z ⊤) ha).trans ((gs_res r z le trivial _).trans e₁)
  rw [e₂, Units.inv_mul_cancel_right]

section Geometry

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)

omit [IsDomain R] in
theorem eSec_fstG (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] :
    eSec (thickObj R I e G) ≫ (fstG I e G).left = thick R I e ≫ eSec G := by
  show eSec (thickObj R I e G) ≫ pullback.fst G.hom (thick R I e) = _
  simp [eSec]

theorem eSec_pG {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (g : GtCoord I D e G) :
    eSec (thickObj R I e G) ≫ g.pG.left = thick R I e ≫ eSec D.P.A := by
  have := g.q_hom
  have h : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (·.left) (IsMonHom.one_hom g.q)
  rw [← eSec_fstG I e D.P.A, ← h, Category.assoc]
  rfl

theorem formEq_zero (D : DegPre R) (k : ℕ) (α : D.X) :
    FormEq (fun i => eSec D.P.A ≫ D.famφB α i) (DegPre.famε k) (fun _ : PUnit => eSec D.P.A)
      (fun _ => (k : ℤ) * 1) := by
  intro U _ f
  have a₀ : eSec D.P.A ≫ D.famφB α 0 = eSec D.P.A := Category.comp_id _
  have a₁ : eSec D.P.A ≫ D.famφB α 1 = eSec D.P.A ≫ D.famφB α 2 := by
    have : η[D.P.A] ≫ ((𝟙 D.P.A) * (toUnit _ ≫ D.c α)) = η[D.P.A] ≫ (toUnit _ ≫ D.c α) := by
      rw [MonObj.comp_mul, Category.comp_id]
      have : η[D.P.A] = (1 : 𝟙_ _ ⟶ D.P.A) := by simp [Hom.one_def]
      rw [this, _root_.one_mul]
    exact congrArg (fun z => z.left) this
  have a₃ : eSec D.P.A ≫ D.famφB α 3 = eSec D.P.A := by
    have : η[D.P.A] ≫ (toUnit D.P.A ≫ η[D.P.A]) = η[D.P.A] := by
      rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
    exact congrArg (fun z => z.left) this
  rw [Fin.prod_univ_four, Fintype.prod_unique]
  simp only [a₀, a₁, a₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, DegPre.famε, Matrix.cons_val]
  module

theorem exists_value (D : DegPre R) (k : ℕ) (α : D.X) (g : D.SecB k α) :
    ∃ a : R, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good D.P.L z J →
      sval g (r ≫ eSec D.P.A) z J = cst r z a * (val (L := D.P.L) D.rig r z J ^ k).val := by
  obtain ⟨a, ha⟩ := exists_coeff (A := R) D.P.isLB g (eSec D.P.A) (GeneratorPullback.powGen D.P.L _ _ D.rig k)
    (powGen_isGen _ _ _ _ D.rig_gen k) (formEq_zero D k α)
  exact ⟨a, fun Z r z J hJ => (ha Z r z J hJ).trans (by rw [val_pow])⟩

end Geometry

section Congruence

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)


variable (I G) in
omit [IsDomain R] in
abbrev unitE (e : ℕ) : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e G).left := eSec (thickObj R I e G)

theorem wv_rig (e : ℕ) (z : Sp (R ⧸ I ^ (e + 1))) {J J'} (hJ : Good D.toPre.P.L z J) (hJ' : Good U.LG.L z J') :
    wv U e (unitE I G e) z (J (unitE I G e ≫ pGl U e)) (J' (thick R I e ≫ eSec G)) *
      val (L := U.LG.L) U.LG.rig (thick R I e) z J' = val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J := by
  have hp : unitE I G e ≫ pGl U e = thick R I e ≫ eSec D.toPre.P.A := eSec_pG I (U.gt e)
  have hf : unitE I G e ≫ fGl I G e = thick R I e ≫ eSec G := eSec_fstG I e G
  rw [hp]
  have m₁ : z ∈ unitE I G e ⁻¹ᵁ
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => J (thick R I e ≫ eSec D.toPre.P.A)) ⊓
        (U.LG.L.pull (fstG I e G).left).U (fun _ => J' (thick R I e ≫ eSec G))) :=
    ⟨mem_pull.2 ((congrArg (fun q => q z ∈ D.toPre.P.L.U (J (thick R I e ≫ eSec D.toPre.P.A))) hp).mpr (hJ _)),
      mem_pull.2 ((congrArg (fun q => q z ∈ U.LG.L.U (J' (thick R I e ≫ eSec G))) hf).mpr (hJ' _))⟩
  have m₂ : z ∈ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => J' (thick R I e ≫ eSec G)) :=
    mem_pull.2 (hJ' (thick R I e ≫ eSec G))
  have m₃ : z ∈ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U
      (fun _ => J (thick R I e ≫ eSec D.toPre.P.A)) := mem_pull.2 (hJ (thick R I e ≫ eSec D.toPre.P.A))
  have W := congrArg (gm (𝟙 _) z _) (U.w_rig e (fun _ => J (thick R I e ≫ eSec D.toPre.P.A),
    fun _ => J' (thick R I e ≫ eSec G)) (_ ⊓ _ ⊓ _) (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
    inf_le_right)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ _ z _ _ _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _)
    (gm_rp₁ _ z _ _ _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _))).symm.trans (W.trans (gm_rp₁ _ z _ _ _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _))

theorem value_sub_sum_mem (e k : ℕ) (σ : H0 U.LG.L k) (g : ∀ α : D.toPre.X, D.toPre.SecB k α)
    (hE : U.ExpandsAt e k σ g) (x : R)
    (hx : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good U.LG.L z J →
      sval σ (r ≫ eSec G) z J = cst r z x * (val (L := U.LG.L) U.LG.rig r z J ^ k).val)
    (a : D.toPre.X → R)
    (ha : ∀ α (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good D.toPre.P.L z J →
      sval (g α) (r ≫ eSec D.toPre.P.A) z J = cst r z (a α) * (val (L := D.toPre.P.L) D.toPre.rig r z J ^ k).val) :
    ∃ S : Finset D.toPre.X, ∀ T : Finset D.toPre.X, S ⊆ T → x - ∑ α ∈ T, a α ∈ I ^ (e + 1) := by
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ g hE
  have hp : unitE I G e ≫ pGl U e = thick R I e ≫ eSec D.toPre.P.A := eSec_pG I (U.gt e)
  have hf : unitE I G e ≫ fGl I G e = thick R I e ≫ eSec G := eSec_fstG I e G
  have hc : ∀ (z : Sp (R ⧸ I ^ (e + 1))) (c : R),
      cst (thick R I e) z c = cst (𝟙 _) z (Ideal.Quotient.mk (I ^ (e + 1)) c) := fun z c => H1.gs_spec _ z c
  refine ⟨S, fun T hT => ?_⟩
  rw [← Ideal.Quotient.eq]
  refine H1.cst_ext fun z => ?_
  rw [← hc, ← hc, cst_sum]
  choose J hJ using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
  choose J' hJ' using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ G.left => exists_chart U.LG.isLB (ψ z)
  have hJ : Good D.toPre.P.L z J := hJ
  have hJ' : Good U.LG.L z J' := hJ'
  obtain ⟨h₀, h₁⟩ := hS _ (unitE I G e) z J hJ
  have h₂ := h₁ (J' (thick R I e ≫ eSec G))
    ((congrArg (fun q => q z ∈ U.LG.L.U (J' (thick R I e ≫ eSec G))) hf).mpr (hJ' _))
  have hs : sv U k σ (unitE I G e ≫ fGl I G e) z (J' (thick R I e ≫ eSec G)) =
      cst (thick R I e) z x * (val (L := U.LG.L) U.LG.rig (thick R I e) z J' ^ k).val := by
    rw [hf]
    exact (sval_of σ _ z J' (fun _ => J' (thick R I e ≫ eSec G)) (fun _ => by rw [Category.comp_id])).symm.trans
      (hx _ _ z J' hJ')
  have ht : ∀ α, val (tG U e α) (unitE I G e) z J = 1 := fun α => by
    have := (val_pull hJ (tG U e α) (unitE I G e) (𝟙 _)).symm.trans
      ((val_corr hJ ((U.gt e).t_unit α) _).trans (val_one _))
    rwa [Category.id_comp] at this
  have hg : ∀ α, sval (g α) (unitE I G e ≫ pGl U e) z J =
      cst (thick R I e) z (a α) * (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).val := fun α => by
    rw [hp]; exact ha α _ _ z J hJ
  have hw := wv_rig U e z hJ hJ'
  refine (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).mul_left_inj.1 ?_
  rw [Finset.sum_mul, ← Finset.sum_subset hT (fun α _ hα => (hg α).symm.trans (h₀ α hα))]
  rw [hs, mul_left_comm, ← Units.val_mul, ← mul_pow] at h₂
  refine Eq.trans (by rw [← hw]) (h₂.trans (Finset.sum_congr rfl fun α _ => ?_))
  rw [ht, hg, Units.val_one, _root_.mul_one]

end Congruence

section Value

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]

variable {F} in
theorem le_val_of_mem_pow {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    (n : ℕ) {c : V} (hc : c ∈ maximalIdeal V ^ n) :
    (((n : ℕ) : ℚ) : WithTop ℚ) ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at hc
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  have h : HasVal ϖ (algebraMap V (FractionRing V) (ϖ ^ n)) (n : ℤ) := ⟨1, by simp⟩
  rw [map_mul, map_mul, AddValuation.map_mul, hv _ _ h]
  simpa using le_add_of_nonneg_left (GC.v_alg_nonneg hϖ hv b)

end Value

end ExpansionValueZero

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFamilyLevelOne
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem integralFamily_levelOne : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (θ : Fam D.toPre F 1) (g : ∀ α : D.toPre.X, D.toPre.SecB 1 α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε 1) (θ.s α) (D.toPre.famφB α) (DegPre.famε 1) (g α) (DegPre.prB D.toPre F).left 1) → NuGe D Q F v 1 θ 0 ∧ ∀ χ, χ ≠ 0 → ∃ g' : D.toPre.SecB 1 χ, SecIsMul D.toPre.P.A.hom ϖ (g χ) g' := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v hv θ g hg
  have hν : NuGe D Q F v 1 θ 0 := by
    refine (n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {0} (fun χ => ⟨0, Finset.mem_singleton_self _, χ, by simp⟩) θ 0).2 ?_
    intro α hα
    rw [Finset.mem_singleton] at hα
    subst hα
    refine ⟨1, fun _ => 1, fun _ => g 0, fun _ => θ.s 0, fun _ => hg 0, fun _ => ?_, fun j => ?_⟩
    · rw [QForm.Q_zero hϖ D hQ]; simp
    · simp [DegPre.constBF]
  refine ⟨hν, fun χ hχ => ?_⟩
  obtain ⟨n, a₀, τ, τF, hτ, hva, hsum⟩ := hν χ
  have hb : ∀ i, 0 < v (a₀ i) := fun i => by
    refine lt_of_lt_of_le ?_ (hva i)
    have h1 : (1 : ℚ) ≤ (Q χ : ℚ) := by exact_mod_cast QForm.Q_pos hϖ D hQ hχ
    have h2 : (0 : ℚ) < 0 + (Q χ : ℚ) / ((1 : ℕ) : ℚ) := by simp; exact_mod_cast (by linarith : (0 : ℚ) < (Q χ : ℚ))
    exact_mod_cast h2
  have vc : ∀ (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε 1))) (x : F)
      {Z : Scheme.{0}} (q : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (j), q z ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j →
      gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (DegPre.constBF D.toPre F x _ * t.f j) =
        cst (q ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z x *
          gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (t.f j) := fun t x Z q z j hz =>
    (gs_mul q z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res q z le_top hz _).trans
      (gs_pull q (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _)) rfl)
  have div₁ := H1.dvd_of_comb hϖ D.toPre F v hv (g χ) τ a₀ hb (fun Z q z J hJ =>
    (H1.sval_scal (hg χ) q z hJ).symm.trans
      ((congrArg (gs _ z _) (hsum _)).trans ((H1.gs_sum q z _ (hJ.mem _ q) _).trans (Finset.sum_congr rfl fun i _ =>
        (vc (τF i) (a₀ i) q z _ (hJ.mem _ q)).trans (congrArg₂ (· * ·) rfl (H1.sval_scal (hτ i) q z hJ))))))
  have := D.toPre.P.isAb.smooth
  exact exists_div_sec D.toPre.P.A.hom hϖ.ne_zero (g χ) div₁

end GlobalTheory
end
end

