module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0020
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0022
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FirstPartialLawPushAlongTripleMap
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.PushFirstLaw

section Val
variable {X X' Y Z : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
  (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι)

def isoVal (ψ : Z ⟶ X') : (Z.presheaf.stalk z)ˣ :=
  gm ψ z ((LB.div (L.pull F) L').U (fun _ => J (ψ ≫ F), J' ψ)) (w.s (fun _ => J (ψ ≫ F), J' ψ))

variable {w z J J'}

theorem val_maps (hJ : Good L z J) (hJ' : Good L' z J') {K : Type} [Fintype K] {φ : K → (Y ⟶ X')} {ε : K → ℤ}
    {g : LB.Gen (LB.LinComb L' φ ε)} {b : LB.Gen (LB.LinComb (L.pull F) φ ε)}
    (h : LB.Gen.Maps (LB.linCombIso w φ ε) g b) (r : Z ⟶ Y) :
    gm r z (LB.wchart (L.pull F) φ fun k _ => J ((r ≫ φ k) ≫ F)) (b.s fun k _ => J ((r ≫ φ k) ≫ F)) =
      (∏ k, isoVal w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  have h1 : r z ∈ LB.wchart (L.pull F) φ fun k _ => J ((r ≫ φ k) ≫ F) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ ((r ≫ φ k) ≫ F)
  have hm : r z ∈ LB.wchart (L.pull F) φ (fun k _ => J ((r ≫ φ k) ≫ F)) ⊓ LB.wchart L' φ (fun k => J' (r ≫ φ k)) :=
    ⟨h1, hJ'.mem φ r⟩
  refine (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _)
    (h (fun k _ => J ((r ≫ φ k) ≫ F), fun k => J' (r ≫ φ k)))).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have ha : (φ a) (r z) ∈ (L.pull F).U (fun _ => J ((r ≫ φ a) ≫ F)) ⊓ L'.U (J' (r ≫ φ a)) :=
    ⟨LB.wchart_le (L.pull F) φ _ a hm.1, LB.wchart_le L' φ _ a hm.2⟩
  exact (gm_res r z _ hm _).trans (gm_pull r (φ a) z _ ha _)

theorem val_carries (hJ : Good L z J) (hJ' : Good L' z J') {K : Type} [Fintype K] {φ : K → (Y ⟶ X')} {ε : K → ℤ}
    {g : LB.Gen (LB.LinComb L' φ ε)} {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)}
    (h : Carries L F w φ ε g g') (r : Z ⟶ Y) :
    val g' r z J = (∏ k, isoVal w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  refine Eq.trans ?_ (val_maps hJ hJ' h r)
  rw [val_of g' r z J (fun k => J ((r ≫ φ k) ≫ F)) (fun k => by rw [Category.assoc])]
  have h1 : r z ∈ LB.wchart (L.pull F) φ fun k _ => J ((r ≫ φ k) ≫ F) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ ((r ≫ φ k) ≫ F)
  exact (gm_res r z _ h1 _).symm

end Val

section Cube
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]

theorem val_theta (m : CubeMap G' G) {L : LB G.left} {L' : LB G'.left} {w : LB.Iso L' (L.pull m.F)}
    {c : LB.Gen (Theta G L)} {c' : LB.Gen (Theta G' L')}
    (h : LB.Gen.Maps (LB.linCombIso w (thφ G' (x3 G')) thε) c' (m.thetaPull L c))
    {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ G.left) → L.ι} {J' : (Z ⟶ G'.left) → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J')
    (r : Z ⟶ (G3 G').left) :
    val (φ := thφ G (x3 G)) (ε := thε) c (r ≫ m.F3) z J =
      (∏ k, isoVal w z J J' (r ≫ thφ G' (x3 G') k) ^ thε k) * val (φ := thφ G' (x3 G')) (ε := thε) c' r z J' := by
  refine Eq.trans ?_ (val_maps hJ hJ' h r)
  have e : ∀ k : thK, (r ≫ m.F3) ≫ thφ G (x3 G) k = (r ≫ thφ G' (x3 G') k) ≫ m.F := fun k => by
    rw [Category.assoc, Category.assoc]
    exact congrArg (r ≫ ·) (m.psum_comm k.down).symm
  refine (val_of (φ := thφ G (x3 G)) (ε := thε) c (r ≫ m.F3) z J (fun k => J ((r ≫ thφ G' (x3 G') k) ≫ m.F))
    (fun k => by rw [e])).trans ?_
  have h1 : r z ∈ LB.wchart (L.pull m.F) (thφ G' (x3 G')) fun k _ => J ((r ≫ thφ G' (x3 G') k) ≫ m.F) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ ((r ≫ thφ G' (x3 G') k) ≫ m.F)
  exact ((gm_res r z _ h1 _).trans (gm_pull r m.F3 z _ (m.theta_le L _ h1) _)).symm

end Cube

theorem lift_cubeMap {S : Scheme.{0}} {G' G T : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (m : CubeMap G' G) (a : Fin 3 → (T ⟶ G')) (b : Fin 3 → (T ⟶ G)) (h : ∀ i, (b i).left = (a i).left ≫ m.F) :
    (lift (b 0) (lift (b 1) (b 2))).left = (lift (a 0) (lift (a 1) (a 2))).left ≫ m.F3 := by
  have k : ∀ i : Fin 3, (x3 G' i).left ≫ m.F = m.F3 ≫ (x3 G i).left := fun i => by
    have e := m.psum_comm {i}
    have p : psum G (x3 G) {i} = x3 G i * 1 := by fin_cases i <;> rfl
    have p' : psum G' (x3 G') {i} = x3 G' i * 1 := by fin_cases i <;> rfl
    rwa [p, p', _root_.mul_one, _root_.mul_one] at e
  have la : ∀ i : Fin 3, lift (a 0) (lift (a 1) (a 2)) ≫ x3 G' i = a i := fun i => by
    fin_cases i <;> simp [x3]
  have k' : ∀ i : Fin 3, ((lift (a 0) (lift (a 1) (a 2))).left ≫ m.F3) ≫ (x3 G i).left = (b i).left := fun i => by
    rw [Category.assoc, ← k, ← Category.assoc, ← Over.comp_left, la, h]
  let q : T ⟶ G3 G := Over.homMk ((lift (a 0) (lift (a 1) (a 2))).left ≫ m.F3) (by
    rw [← Over.w (x3 G 0), ← Category.assoc, k', Over.w])
  have hq : ∀ i : Fin 3, q ≫ x3 G i = b i := fun i => Over.OverMorphism.ext (k' i)
  have : lift (b 0) (lift (b 1) (b 2)) = q := by
    refine CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (hq 0).symm) ?_
    rw [lift_snd]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [lift_fst, Category.assoc]; exact (hq 1).symm
    · rw [lift_snd, Category.assoc]; exact (hq 2).symm
  rw [this]
  rfl

theorem rearrange {U : Type} [CommGroup U] (a b c u p q r : U) :
    a * (b⁻¹ * c⁻¹) * (u * (p * (q⁻¹ * r⁻¹))) = u * (a * p * ((b * q)⁻¹ * (c * r)⁻¹)) := by
  simp only [mul_inv]
  ac_rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem val_scaleG {X0 : Scheme.{0}} (t : SAB H X0) {Y Z : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) (c : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)


open GlobalTheory.SecondPartialLaw in
theorem formal_sum {X0 : Scheme.{0}} {t : SAB H X0} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ}
    {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {κ : Type} [Fintype κ]
    {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uv : κ → Fin d → S} (hch : IsChartG t x0 d F act tg uv x) (m : ℕ)
    {U : Type} [CommGroup U] (h : ((jOG x0 d m 3).left ⟶ t.G.left) → U)
    (P : (Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) → U)
    (hP : ∀ φ, P φ = ∏ k, h ((Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] k) ^ cε 2 k) :
    ∏ k : thK.{0}, h ((lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left ≫
        thφ t.G (x3 t.G) k) ^ thε k =
      P ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] *
        ((P ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])⁻¹ *
          (P ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])⁻¹) := by
  have hP' : ∀ (φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (a b : jOG x0 d m 3 ⟶ t.G),
      Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 0 p.2)) ≫ x m = a →
      Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 1 p.2)) ≫ x m = b →
      P φ = h (1 : jOG x0 d m 3 ⟶ t.G).left * (h a.left)⁻¹ * (h b.left)⁻¹ * h (b * a).left := by
    rintro φ _ _ rfl rfl
    rw [← pt_sub m φ 0, ← pt_sub m φ 1]
    have e1 := Finset.prod_congr (s₁ := Finset.univ) rfl fun (k : ULift.{0} (Finset (Fin 2))) _ =>
      congrArg (fun q => h q ^ cε 2 k) (pe_pt (t := t) (x := x) m (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) k)
    have e2 := prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)
      ![Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) ≫ jptG t x0 d x m (0 : Fin 2),
        Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) ≫ jptG t x0 d x m (1 : Fin 2)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one] at e2
    exact (hP φ).trans (e1.trans e2)
  rw [hP' ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] _ _
      (pt_law hch m ![0, 1]) (pt_X m 2),
    hP' ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] _ _ (pt_X m 0) (pt_X m 2),
    hP' ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] _ _ (pt_X m 1) (pt_X m 2)]
  refine (Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ thε k) (th_pt _ _ _ k)).trans
    ((prod_cube3 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left) _).trans ?_)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, _root_.mul_one]
  generalize jptG t x0 d x m (0 : Fin 3) = a
  generalize jptG t x0 d x m (1 : Fin 3) = b
  generalize jptG t x0 d x m (2 : Fin 3) = c
  rw [_root_.mul_comm c (a * b), _root_.mul_comm c a, _root_.mul_comm c b, _root_.mul_assoc a b c]
  apply ofMul_eq
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.PushFirstLaw

namespace GlobalTheory

open PushFirstLaw

theorem famPh1_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ph : PS V 3 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamPh1 t (𝟙 (Sp V)) d x F ph e → FamPh1 t' (𝟙 (Sp V)) d x' F ph e' := by
  intro E _ _ _ H V _ t t' n w d x x' e e' hw hx _ hp F act κ _ tg uv ph hch h m
  obtain ⟨u, hu, hcor⟩ := h m
  obtain ⟨-, c, -, hc, hcar⟩ := hp m
  refine ⟨u, hu, corr_of_val t'.PP.isLB fun y J hJ => ?_⟩
  obtain ⟨J', hJ', -⟩ := exists_good t.PP.L t.PP.isLB y (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim)
    (fun a => a.elim)
  have k := val_corr hJ' hcor (𝟙 _)
  have hpe : ∀ φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V,
      val (peG t' (𝟙 (Sp V)) d x' e' m φ) (𝟙 _) y J =
        (∏ k, isoVal w y J J' ((Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
          cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] k) ^ cε 2 k) *
          val (peG t (𝟙 (Sp V)) d x e m φ) (𝟙 _) y J' := fun φ => by
    refine (val_pull hJ _ _ _).trans ((val_corr hJ hc _).symm.trans ((val_carries hJ hJ' hcar _).trans
      (congrArg₂ (· * ·) ?_ (val_pull hJ' _ _ _).symm)))
    rw [Category.id_comp]
  have hl := lift_cubeMap n.cm (fun i => jptG t (𝟙 (Sp V)) d x m i) (fun i => jptG t' (𝟙 (Sp V)) d x' m i) (fun i => by
    simp only [jptG, Over.comp_left, hx m, Category.assoc])
  have hs := formal_sum hch m (isoVal w y J J') _ (fun _ => rfl)
  have k2 := (val_pull hJ' _ _ _).symm.trans (k.trans ((val_scaleG t hJ' _ _ _).trans (congrArg (_ * ·)
    ((val_mul hJ' _ _ _).trans (congrArg (_ * ·) ((val_mul hJ' _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))))
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_scaleG t' hJ _ _ _).trans (congrArg (_ * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hpe _) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) (hpe _)))
        ((val_inv _ _).trans (congrArg (·⁻¹) (hpe _))))))))).symm)
  refine (congrArg (fun r => val (φ := thφ t'.G (x3 t'.G)) (ε := thε) t'.cub.t r y J)
    ((Category.id_comp _).trans hl)).trans ((val_theta n.cm hw.2 hJ hJ' _).trans ((congrArg₂ (· * ·) hs
      ((congrArg (fun r => val (φ := thφ t.G (x3 t.G)) (ε := thε) t.cub.t r y J') (Category.id_comp _)).symm.trans k2)).trans
        (rearrange _ _ _ _ _ _ _)))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalChartJetRelUnitOneOnAxes
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ChartCmp.Axes

variable {R : Type} [CommRing R]

theorem jEq_iff_order {σ : Type} (m : ℕ) (f g : MvPowerSeries σ R) :
    JEq m f g ↔ ((m + 1 : ℕ) : ℕ∞) ≤ MvPowerSeries.order (f - g) := by
  constructor
  · intro h
    refine MvPowerSeries.nat_le_order fun e he => ?_
    rw [map_sub, h e (by omega), sub_self]
  · intro h e he
    have : MvPowerSeries.coeff e (f - g) = 0 :=
      MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le he) h)
    rwa [map_sub, sub_eq_zero] at this

theorem jEq_mul_right {σ : Type} {m : ℕ} {f g : MvPowerSeries σ R} (u : MvPowerSeries σ R) (h : JEq m f g) :
    JEq m (f * u) (g * u) := by
  rw [jEq_iff_order] at h ⊢
  rw [← sub_mul]
  exact h.trans (le_self_add.trans MvPowerSeries.le_order_mul)

theorem jEq_ev {d n n' m : ℕ} (a : Fin n → Pt R n' d) (ha : ∀ j, GP (a j)) {f g : PS R n d} (h : JEq m f g) :
    JEq m (ev a f) (ev a g) := by
  classical
  intro e he
  unfold ev
  rw [MvPowerSeries.coeff_subst (gt_hasSubst a ha), MvPowerSeries.coeff_subst (gt_hasSubst a ha)]
  refine finsum_congr fun c => ?_
  by_cases hc : c.degree ≤ m
  · rw [h c hc]
  · have : MvPowerSeries.coeff e (c.prod fun s k => (a s.1 s.2) ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_prod _ _)
      have h1 : ((c.degree : ℕ) : ℕ∞) ≤ ∑ s ∈ c.support, MvPowerSeries.order ((a s.1 s.2) ^ c s) := by
        rw [Finsupp.degree_apply, Nat.cast_sum]
        refine Finset.sum_le_sum fun s _ => ?_
        exact MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (ha s.1 s.2)
      refine lt_of_lt_of_le ?_ h1
      exact_mod_cast (by omega : e.degree < c.degree)
    rw [this, smul_zero, smul_zero]

theorem jEq_one_of_idem {σ : Type} {m : ℕ} {e : MvPowerSeries σ R} (hu : IsUnit (MvPowerSeries.constantCoeff e))
    (h : JEq m e (e * e)) : JEq m e 1 := by
  obtain ⟨u, rfl⟩ := MvPowerSeries.isUnit_iff_constantCoeff.2 hu
  have := jEq_mul_right (↑u⁻¹ : MvPowerSeries σ R) h
  rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one] at this
  exact fun e he => (this e he).symm

theorem vec3 {d m n : ℕ} (V : Fin m → Pt R n d) (a b c : Pt R m d) :
    (fun j => evP V (![a, b, c] j)) = ![evP V a, evP V b, evP V c] := by
  funext j; fin_cases j <;> rfl

theorem addOf_zero {d n : ℕ} (F : Fin d → PS R 2 d) (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0) :
    addOf F (0 : Pt R n d) 0 = 0 := by
  funext i
  change MvPowerSeries.subst (fun p : Fin 2 × Fin d => (![(0 : Pt R n d), 0] p.1) p.2) (F i) = 0
  have e : (fun p : Fin 2 × Fin d => (![(0 : Pt R n d), 0] p.1) p.2) = 0 := by
    funext p
    obtain ⟨j, l⟩ := p
    fin_cases j <;> rfl
  rw [e]
  exact MvPowerSeries.subst_zero_of_constantCoeff_zero (hF i)

theorem ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one {d n : ℕ} (f : PS R 3 d) (hf : ev (n := 2) ![0, pt R d 0, pt R d 1] f = 1) (z : Pt R n d) (hz : GP z) :
    ev ![0, 0, z] f = 1 := by
  have hV : ∀ j, GP (![(0 : Pt R n d), z] j) := pair_points_zero_constant gp_zero₂ hz
  have := congrArg (ev ![0, z]) hf
  rw [gt_ev_ev' _ _ hV (triple_points_zero_constant gp_zero₂ (gp_pt 0) (gp_pt 1)), vec3, evP_zero _ hV, evP_pt _ hV,
    evP_pt _ hV, ev_one] at this
  exact this

theorem ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one {d n : ℕ} (f : PS R 3 d) (hf : ev (n := 2) ![pt R d 0, pt R d 1, 0] f = 1) (z : Pt R n d) (hz : GP z) :
    ev ![z, 0, 0] f = 1 := by
  have hV : ∀ j, GP (![z, (0 : Pt R n d)] j) := pair_points_zero_constant hz gp_zero₂
  have := congrArg (ev ![z, 0]) hf
  rw [gt_ev_ev' _ _ hV (triple_points_zero_constant (gp_pt 0) (gp_pt 1) gp_zero₂), vec3, evP_zero _ hV, evP_pt _ hV,
    evP_pt _ hV, ev_one] at this
  exact this

end GlobalTheory.ChartCmp.Axes


open GlobalTheory.ChartCmp.Axes in
theorem GlobalTheory.ChartCmp.jRel_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ) (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d), JRel m B B' φ φi ε → MvPowerSeries.constantCoeff ε = 1 ∧ JEq m (ev (n := 1) ![0, pt R (n := 1) d 0] ε) 1 ∧ JEq m (ev (n := 1) ![pt R (n := 1) d 0, 0] ε) 1 := by
  intro R _ d O _ _ m B B' φ φi ε h
  have hφ : GP φ := h.inv.1
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt R (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt R n d) := gp_zero₂
  have hc : ∀ {n : ℕ} (j : Fin n), GP (comp1 φ (pt R (n := n) d j)) := fun j => gp_comp1 φ _ hφ (hp j)
  have h1 : JEq m (ev (n := 1) ![0, pt R (n := 1) d 0] ε) 1 := by
    have hV : ∀ j, GP (![(0 : Pt R 1 d), 0, pt R (n := 1) d 0] j) := triple_points_zero_constant hz hz (hp 0)
    have H := jEq_ev _ hV h.ph1
    rw [gt_ev_mul _ hV, gt_ev_mul _ hV, gt_ev_mul _ hV, ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one _ B'.cocycleLeft_zero_fst _ (hp 0), _root_.one_mul,
      gt_ev_ev' _ _ hV (pair_points_zero_constant (gp_addOf _ B'.G.const _ _ (hp 0) (hp 1)) (hp 2)),
      gt_ev_ev' _ _ hV (triple_points_zero_constant (hc 0) (hc 1) (hc 2)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)),
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 1) (hp 2)), vec3, eval_pair_points, eval_pair_points, eval_pair_points,
      evP_addOf _ hV _ _ _ (hp 0) (hp 1), evP_comp1 _ hV _ _ (hp 0), evP_comp1 _ hV _ _ (hp 1),
      evP_comp1 _ hV _ _ (hp 2), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at H
    change JEq m (ev ![addOf B'.G.F 0 0, pt R (n := 1) d 0] ε)
      (ev ![comp1 φ 0, comp1 φ 0, comp1 φ (pt R (n := 1) d 0)] B.ph1 *
        (ev ![0, pt R (n := 1) d 0] ε * ev ![0, pt R (n := 1) d 0] ε)) at H
    rw [addOf_zero _ B'.G.const, gt_comp1_zero φ hφ, ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one _ B.cocycleLeft_zero_fst _ (hc 0), _root_.one_mul] at H
    refine jEq_one_of_idem ?_ H
    rw [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0))]
    exact h.unit
  have h2 : JEq m (ev (n := 1) ![pt R (n := 1) d 0, 0] ε) 1 := by
    have hV : ∀ j, GP (![pt R (n := 1) d 0, (0 : Pt R 1 d), 0] j) := triple_points_zero_constant (hp 0) hz hz
    have H := jEq_ev _ hV h.ph2
    rw [gt_ev_mul _ hV, gt_ev_mul _ hV, gt_ev_mul _ hV, ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one _ B'.cocycleRight_zero_thd _ (hp 0), _root_.one_mul,
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (gp_addOf _ B'.G.const _ _ (hp 1) (hp 2))),
      gt_ev_ev' _ _ hV (triple_points_zero_constant (hc 0) (hc 1) (hc 2)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 1)),
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)), vec3, eval_pair_points, eval_pair_points, eval_pair_points,
      evP_addOf _ hV _ _ _ (hp 1) (hp 2), evP_comp1 _ hV _ _ (hp 0), evP_comp1 _ hV _ _ (hp 1),
      evP_comp1 _ hV _ _ (hp 2), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at H
    change JEq m (ev ![pt R (n := 1) d 0, addOf B'.G.F 0 0] ε)
      (ev ![comp1 φ (pt R (n := 1) d 0), comp1 φ 0, comp1 φ 0] B.ph2 *
        (ev ![pt R (n := 1) d 0, 0] ε * ev ![pt R (n := 1) d 0, 0] ε)) at H
    rw [addOf_zero _ B'.G.const, gt_comp1_zero φ hφ, ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one _ B.cocycleRight_zero_thd _ (hc 0), _root_.one_mul] at H
    refine jEq_one_of_idem ?_ H
    rw [gt_const_ev_eq _ (pair_points_zero_constant (hp 0) hz)]
    exact h.unit
  refine ⟨?_, h1, h2⟩
  have := h1 0 (by simp)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_one] at this
  exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalGroupLogEndomorphismLinear
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.LogLinear

variable {k : Type} [CommRing k] {d : ℕ}

theorem eq_zero_of_additive [Algebra ℚ k] (G : FGLaw k d) (g : PS k 1 d)
    (hadd : ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] g =
      ev (n := 2) ![pt k d 0] g + ev (n := 2) ![pt k d 1] g)
    (hlin : ∀ i, coeff (Finsupp.single ((0 : Fin 1), i) 1) g = 0) : g = 0 := by
  have hc {n : ℕ} (x : Pt k n d) (y : Fin 0 → Pt k n d) :
      (Fin.cons x y : Fin (0 + 1) → Pt k n d) = ![x] := by
    funext j
    fin_cases j
    rfl
  refine GlobalTheory.AdditiveSeries.eq_zero_of_additive_of_pderiv k d G 0 g ?_ fun i => ?_
  · simpa only [hc] using hadd
  · rw [hc]
    ext m
    obtain rfl : m = 0 := Subsingleton.elim _ _
    rw [coeff_zero_eq_constantCoeff_apply, gt_const_ev_eq _ (single_point_zero_constant gp_zero₂),
      ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
    simp [hlin i]

theorem ev_sum_C_mul {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (c : Fin d → k)
    (f : Fin d → PS k m d) : ev V (∑ j, C (c j) * f j) = ∑ j, C (c j) * ev V (f j) := by
  unfold ev
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom (gt_hasSubst V hV), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coe_substAlgHom, subst_C]

theorem dLin_comp1 (φ ψ : Pt k 1 d) (hψ : GP ψ) : dLin (comp1 φ ψ) = dLin φ * dLin ψ := by
  ext i j
  refine (FormalCalc.coeff_single_subst
    (a := fun p : Fin 1 × Fin d => (![ψ] : Fin 1 → Pt k 1 d) p.1 p.2)
    (fun p => single_point_zero_constant hψ p.1 p.2) (φ i) _).trans ?_
  rw [Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.mul_apply]
  rfl

theorem germ_comp_additive_at_points {n : ℕ} (G : FGLaw k d) (ψ : Pt k 1 d)
    (hψ : comp1 ψ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ψ (pt k (n := 2) d 0) + comp1 ψ (pt k (n := 2) d 1))
    (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    comp1 ψ (G.add a b) = comp1 ψ a + comp1 ψ b := by
  have hV := pair_points_zero_constant ha hb
  have e := congrArg (evP ![a, b]) hψ
  have e2 : ∀ u v : Pt k 2 d, evP ![a, b] (u + v) = evP ![a, b] u + evP ![a, b] v := fun u v =>
    funext fun i => gt_ev_add _ hV _ _
  rw [e2, evP_comp1 _ hV _ _ (gp_addOf _ G.const _ _ (gp_pt 0) (gp_pt 1)),
    evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1), evP_comp1 _ hV _ _ (gp_pt 0),
    evP_comp1 _ hV _ _ (gp_pt 1), evP_pt _ hV, evP_pt _ hV] at e
  exact e

theorem formalGroup_log_endomorphism_linear :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ℓ α : Pt k 1 d),
      (∀ i, MvPowerSeries.constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
      comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
        comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
      (∀ i, MvPowerSeries.constantCoeff (α i) = 0) →
      comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
        G.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)) →
      ∀ i, comp1 ℓ α i = ∑ j, MvPowerSeries.C (dLin α i j) * ℓ j := by
  intro k _ _ d G ℓ α _ h1 hadd hα hhom i
  have hS : GP (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) :=
    gp_addOf _ G.const _ _ (gp_pt _) (gp_pt _)
  have hev (a : Pt k 2 d) (ha : GP a) :
      ev ![a] (comp1 ℓ α i - ∑ j, C (dLin α i j) * ℓ j) =
        comp1 ℓ (comp1 α a) i - ∑ j, C (dLin α i j) * comp1 ℓ a j := by
    rw [gt_ev_sub _ (single_point_zero_constant ha), ev_sum_C_mul _ (single_point_zero_constant ha), ← gt_comp1_comp1 ℓ α hα a ha]
    rfl
  rw [← sub_eq_zero]
  refine eq_zero_of_additive G _ ?_ fun l => ?_
  · rw [hev _ hS, hev _ (gp_pt _), hev _ (gp_pt _), hhom, hadd,
      germ_comp_additive_at_points G ℓ hadd _ _ (gp_comp1 α _ hα (gp_pt _)) (gp_comp1 α _ hα (gp_pt _))]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  · have h2 : dLin (comp1 ℓ α) i l = (dLin α * dLin ℓ) i l := by
      rw [dLin_comp1 ℓ α hα, h1, one_mul, mul_one]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, sub_eq_zero]
    simp only [coeff_C_mul]
    exact h2

end GlobalTheory.LogLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameFirstPartialLawIffPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

theorem GlobalTheory.units_cancel_first_law {U : Type} [CommGroup U] (g p q r abc ab ac bc a b c o : U) :
    g * ((abc * ab⁻¹ * c⁻¹ * o * p) * ((ac * a⁻¹ * c⁻¹ * o * q)⁻¹ * (bc * b⁻¹ * c⁻¹ * o * r)⁻¹)) =
      (abc * ab⁻¹ * ac⁻¹ * bc⁻¹ * a * b * c * o⁻¹) * (g * (p * (q⁻¹ * r⁻¹))) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel


open GlobalTheory.FramePartialLawTwo in
theorem GlobalTheory.frame_first_partial_law_iff_pullback :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (F : Fin d → PS S 2 d) (ph1 : PS S 3 d), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)) → ((∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))) ↔ (∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L (thφ t'.G (x3 t'.G)) thε t'.cub.t (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)) (lift (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)))).left) (scaleGenG t' _ _ (unitΓ u) (LB.mulGen t'.PP.L _ _ _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t'.PP.L _ _ _ _ (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))))) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w _ d x x' hx hθ e e' _ _ he F ph1 hF law
  refine forall_congr' fun m => exists_congr fun u => and_congr_right fun _ => ?_
  obtain ⟨c₁, h₁, h₂⟩ := he m
  refine corr_iff_of_val t.PP.isLB t'.PP.isLB fun y J J' hJ hJ' => ?_
  have eθ := val_cubic hθ (jptG t x0 d x m (0 : Fin 3)) (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3))
    (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3))
    (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)) (jpt_push hx m 0) (jpt_push hx m 1) (jpt_push hx m 2) hJ hJ'
  have eA := val_frame h₁ h₂ ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)] _ _
    (subst_law t' _ d x' m F hF (law m) ![0, 1]) (subst_X t' _ d x' m 2) hJ hJ'
  have eB := val_frame h₁ h₂ ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] _ _
    (subst_X t' _ d x' m 0) (subst_X t' _ d x' m 2) hJ hJ'
  have eC := val_frame h₁ h₂ ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] _ _
    (subst_X t' _ d x' m 1) (subst_X t' _ d x' m 2) hJ hJ'
  refine ⟨_, eθ, ?_⟩
  refine ((GermB.val_scale t _ _ _ _ _ _ _ hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) eA ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) eB))
      ((val_inv _ _).trans (congrArg (·⁻¹) eC)))))))).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) rfl ((GermB.val_scale t' _ _ _ _ _ _ _ hJ').trans
    (congrArg₂ (· * ·) rfl ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl ((val_mul hJ' _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))).symm)
  exact GlobalTheory.units_cancel_first_law _ _ _ _ _ _ _ _ _ _ _ _
end
end

