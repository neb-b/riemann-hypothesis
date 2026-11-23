module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartEqOfThetaOperatorEq
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PhiBase

theorem exists_pull_sec {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (t : Y' ⟶ Y) (g : Y' ⟶ X)
    (hg : t ≫ f = g) (θ : LB.Sec (L.pull f)) : ∃ θ' : LB.Sec (L.pull g),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
        sval (L := L) (φ := fun _ : PUnit => g) (ε := fun _ => 1) θ' r z J =
          sval (L := L) (φ := fun _ : PUnit => f) (ε := fun _ => 1) θ (r ≫ t) z J := by
  subst hg
  obtain ⟨θ', h⟩ := exists_sec hL (φ' := fun _ : PUnit => t ≫ f) (ε' := fun _ => 1)
    (fun U _ h => by simp [Fintype.prod_sum_type])
    (pullMulSec (L := L) (φ := fun _ : PUnit => f) (ε := fun _ => 1) θ t (LB.oneGen L (Y := Y'))
      (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm))
  refine ⟨θ', fun Z r z J hJ => ?_⟩
  refine (h Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one]

theorem trPt_inv_comp {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (b : TF (R := R) F ⟶ D.P.A) :
    DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, DVR.tr_fst, DVR.tr_fst, Category.id_comp]
  · have : (DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b) ≫ DegPre.prB D F = DegPre.prB D F := by
      rw [Category.assoc, DVR.tr_pr, MonObj.comp_mul, DVR.tr_pr, ← Category.assoc, DVR.tr_fst, _root_.mul_assoc,
        ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one]
    exact this.trans (Category.id_comp _).symm

theorem prod_comp_fam_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (t : DegPre.BF D F ⟶ DegPre.BF D F) {U : Type} [CommGroup U]
    (h : ((DegPre.BF D F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (t.left ≫ DegPre.famφ D F 0 i) ^ DegPre.famε k i = h (t ≫ DegPre.prB D F).left ^ k :=
  ThetaPow.prod_fam_zero D F k (fun q => h (t.left ≫ q))

theorem b_eq_of_phiRel : GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → p'.y = p.y → p.g.b = p'.g.b := by
  intro hG hT R _ _ D hB F _ _ n hn p p' w w' hw hw' H hy
  have hL := D.P.isLB
  obtain ⟨θ, σ, hθ, hσ⟩ := ThetaPow.exists_theta_pow hT R D F n hn
  obtain ⟨s, hs, -⟩ := FamFree.exists_fam_single hG hB hn 0 σ
  obtain ⟨s', h₁, h₂⟩ := H s
  have v₁ := (DVR.phiRel_iff hG p w hw s s').1 h₁ 0 p.y (zero_add _) _ (𝟙 _)
  have v₂ := (DVR.phiRel_iff hG p' w' hw' s s').1 h₂ 0 p.y ((zero_add _).trans hy) _ (𝟙 _)
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := DVR.gen_phi hG p w hw 0
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := DVR.gen_phi hG p' w' hw' 0
  obtain ⟨θ₁, hθ₁⟩ := exists_pull_sec hL (DegPre.prB D F).left (DegPre.trPt D F p.g.b).left
    (DegPre.trPt D F p.g.b ≫ DegPre.prB D F).left rfl θ
  obtain ⟨θ₂, hθ₂⟩ := exists_pull_sec hL (DegPre.prB D F).left (DegPre.trPt D F p'.g.b).left
    (DegPre.trPt D F p'.g.b ≫ DegPre.prB D F).left rfl θ
  obtain ⟨v, hvg, hvv⟩ := exists_gen hL (K' := Fin 2)
    (φ' := ![(DegPre.trPt D F p.g.b ≫ DegPre.prB D F).left, (DegPre.trPt D F p'.g.b ≫ DegPre.prB D F).left])
    (ε' := ![(n : ℤ), -(n : ℤ)]) (fun U _ h => by
      have a := prod_comp_fam_zero D F n (DegPre.trPt D F p.g.b) h
      have a' := prod_comp_fam_zero D F n (DegPre.trPt D F p'.g.b) h
      have c : ∏ i, h (DegPre.famφ D F (0 + p'.y) i) ^ DegPre.famε n i =
        ∏ i, h (DegPre.famφ D F (0 + p.y) i) ^ DegPre.famε n i := by rw [hy]
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ c (DVR.prod_neg _ _ a'))
        (DVR.prod_neg _ _ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
          (c := ∏ i, h (DegPre.famφ D F (0 + p.y) i) ^ DegPre.famε n i) rfl (DVR.prod_neg _ _ a)))) ?_
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast]
      rw [mul_inv, inv_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul, _root_.mul_comm])
    (LB.mulGen D.P.L _ _ _ _ u' (LB.invGen D.P.L _ _ u))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu' (DVR.invGen_isGen _ _ _ _ hu))
  obtain ⟨hI, hN⟩ := degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk R D F
  have hne : ∃ j, θ₂.f j ≠ 0 := by
    by_contra h0
    have h0' : ∀ j, θ₂.f j = 0 := fun j => by_contra fun hj => h0 ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hθ
    refine hj (sec_ext_val (L := D.P.L) (φ := fun _ : PUnit => (DegPre.prB D F).left) (ε := fun _ => 1) (s := θ)
      (s' := DVR.SecOps.secZero) hL (fun y J hJ => ?_) j)
    have e := hθ₂ _ (DegPre.trPt D F p'.g.b⁻¹).left y J hJ
    rw [← Over.comp_left, trPt_inv_comp, Over.id_left] at e
    rw [← e, DVR.UUA.sval_zero_of h0' _ y J (hJ.mem _ _),
      DVR.UUA.sval_zero_of (s := DVR.SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]
  obtain ⟨r, hr, -⟩ := RootUnit.exists_gen_of_pow _ _ hN D.P.L hL _ _ n hn θ₁ θ₂ v hvg hne (fun y J hJ => by
    have e₁ := v₁ y J hJ
    have e₂ := v₂ y J hJ
    rw [← hv u hu hc _ (𝟙 _) y J hJ, hs, hσ _ _ y J hJ] at e₁
    rw [← hv' u' hu' hc' _ (𝟙 _) y J hJ, hs, hσ _ _ y J hJ] at e₂
    have e := e₁.symm.trans e₂
    have f₁ := hθ₁ _ (𝟙 _) y J hJ
    have f₂ := hθ₂ _ (𝟙 _) y J hJ
    simp only [Category.id_comp, Over.id_left] at e f₁ f₂
    rw [← f₁, ← f₂] at e
    rw [hvv _ _ y J hJ, val_mul hJ, val_inv, Units.val_mul, mul_right_comm, _root_.mul_comm (Units.val _)]
    exact ((Units.eq_mul_inv_iff_mul_eq _).2 e))
  exact eq_of_isGen_transl R D F _ _ r hr

end GlobalTheory.PhiBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariantStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.genMaps_linCombIso_of_semiAbelian : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → (Geo.Tor.PMaps wL (thφ G (x3 G)) (thφ G (x3 G)) thε U'.cubG.t U.cubG.t (𝟙 _) ∧ Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] U'.symG U.symG (𝟙 G.left)) → ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom → (U'.gt e).q ≫ β.hom = (U.gt e).q → ∀ u : LB.Iso (D'.toPre.P.L.pull (U'.gt e).pG.left) (D.toPre.P.L.pull (U.gt e).pG.left), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw u r z jM (fun _ => jM') * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL') → ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.toPre.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι), (U.gt e).pG.left (y.left z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.toPre.P.L.U jM' → Geo.Tor.gw u ((τ ≫ (U.gt e).i) * y).left z jM (fun _ => jM') = Geo.Tor.gw u y.left z jM (fun _ => jM') := by
  first | exact @GlobalTheory.comparison_torus_invariant | exact GlobalTheory.comparison_torus_invariant | (intros; apply GlobalTheory.comparison_torus_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNRatioTwist
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem cubN_twist {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (β : A' →* A) (W : A' → U)
    {θ : A → A → A → U} {θ' : A' → A' → A' → U}
    (hθ : ∀ a b d, θ (β a) (β b) (β d) * W (a * b) * W (a * d) * W (b * d) * W 1 =
      W (a * b * d) * W a * W b * W d * θ' a b d) (x y : A') (k : ℕ) :
    cubN θ k 1 (β x) (β y) * W (x ^ k) * W y * (W (x * y) * W 1) ^ k =
      W (x ^ k * y) * W 1 * (W x * W y) ^ k * cubN θ' k 1 x y := by
  induction k with
  | zero => simp only [cubN, Finset.range_zero, Finset.prod_empty, pow_zero, _root_.one_mul, _root_.mul_one]; exact mul_comm _ _
  | succ k ih =>
    have e₁ : cubN θ (k + 1) 1 (β x) (β y) = cubN θ k 1 (β x) (β y) * θ (β (x ^ k)) (β x) (β y) := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, map_pow]
    have e₂ : cubN θ' (k + 1) 1 x y = cubN θ' k 1 x y * θ' (x ^ k) x y := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have H := hθ (x ^ k) x y
    rw [← pow_succ] at H
    rw [e₁, e₂]
    apply mul_right_cancel (b := W (x ^ k) * W (x ^ k * y))
    calc cubN θ k 1 (β x) (β y) * θ (β (x ^ k)) (β x) (β y) * W (x ^ (k + 1)) * W y *
            (W (x * y) * W 1) ^ (k + 1) * (W (x ^ k) * W (x ^ k * y))
          = (cubN θ k 1 (β x) (β y) * W (x ^ k) * W y * (W (x * y) * W 1) ^ k) *
            (θ (β (x ^ k)) (β x) (β y) * W (x ^ (k + 1)) * W (x ^ k * y) * W (x * y) * W 1) := by
          rw [pow_succ (W (x * y) * W 1) k]; ac_rfl
      _ = (W (x ^ k * y) * W 1 * (W x * W y) ^ k * cubN θ' k 1 x y) *
            (W (x ^ (k + 1) * y) * W (x ^ k) * W x * W y * θ' (x ^ k) x y) := by rw [ih, H]
      _ = W (x ^ (k + 1) * y) * W 1 * (W x * W y) ^ (k + 1) * (cubN θ' k 1 x y * θ' (x ^ k) x y) *
            (W (x ^ k) * W (x ^ k * y)) := by
          rw [pow_succ (W x * W y) k]; ac_rfl

theorem cubN_ratio_twist {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (β : A' →* A) (W : A' → U)
    {θ : A → A → A → U} {θ' : A' → A' → A' → U}
    (hθ : ∀ a b d, θ (β a) (β b) (β d) * W (a * b) * W (a * d) * W (b * d) * W 1 =
      W (a * b * d) * W a * W b * W d * θ' a b d) {x y : A'} {N : ℕ} (hx : x ^ N = 1) (hy : y ^ N = 1) {e : U}
    (h : e * cubN θ' N 1 x y = cubN θ' N 1 y x) :
    e * cubN θ N 1 (β x) (β y) = cubN θ N 1 (β y) (β x) := by
  have h₁ := cubN_twist β W hθ x y N
  have h₂ := cubN_twist β W hθ y x N
  simp only [hx, _root_.one_mul] at h₁
  simp only [hy, _root_.one_mul] at h₂
  rw [mul_comm y x, mul_comm (W y) (W x)] at h₂
  have k₁ : cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N =
      (W x * W y) ^ N * cubN θ' N 1 x y := by
    apply mul_right_cancel (b := W 1 * W y)
    calc cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N * (W 1 * W y)
          = cubN θ N 1 (β x) (β y) * W 1 * W y * (W (x * y) * W 1) ^ N := by ac_rfl
      _ = W y * W 1 * (W x * W y) ^ N * cubN θ' N 1 x y := h₁
      _ = (W x * W y) ^ N * cubN θ' N 1 x y * (W 1 * W y) := by ac_rfl
  have k₂ : cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N =
      (W x * W y) ^ N * cubN θ' N 1 y x := by
    apply mul_right_cancel (b := W 1 * W x)
    calc cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N * (W 1 * W x)
          = cubN θ N 1 (β y) (β x) * W 1 * W x * (W (x * y) * W 1) ^ N := by ac_rfl
      _ = W x * W 1 * (W x * W y) ^ N * cubN θ' N 1 y x := h₂
      _ = (W x * W y) ^ N * cubN θ' N 1 y x * (W 1 * W x) := by ac_rfl
  apply mul_right_cancel (b := (W (x * y) * W 1) ^ N)
  calc e * cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N
        = e * (cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N) := mul_assoc _ _ _
    _ = (W x * W y) ^ N * (e * cubN θ' N 1 x y) := by rw [k₁]; ac_rfl
    _ = cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N := by rw [h, k₂]

theorem cubWeil_map : (∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (P : CP G) (P' : CP G') (F : G'.left ⟶ G.left) (hw) (w), IsCPMap P' P f F hw w → ∀ (N : ℕ) (T : Over S') (x y : T ⟶ G') (ζ : Γ(T.left, ⊤)ˣ), CubWeil P'.c N x y ζ → CubWeil P.c N (toBase hw x) (toBase hw y) ζ) := by
  intro S S' f G _ _ G' _ _ P P' F hw w hP N T x y ζ hζ
  obtain ⟨hx, hy, hr⟩ := hζ
  let β := toBaseHom (hw := hw) hP.mul T
  have hβ : ∀ a : T ⟶ G', β a = toBase hw a := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hβ, ← map_pow, hx, map_one]
  · rw [← hβ, ← map_pow, hy, map_one]
  · intro z J hJ
    obtain ⟨J', hJ'⟩ := exists_good_pt P'.L.isLB z
    have hv := (hP.vals T z J' J hJ' hJ (fun a => gw w a.left z (J (a.left ≫ F)) (J' a.left))
      (fun _ => rfl)).2.2
    exact cubN_ratio_twist β (fun a => gw w a.left z (J (a.left ≫ F)) (J' a.left))
      (θ := cubV P.c (T := Over.mk (T.hom ≫ f)) z J) (θ' := cubV P'.c z J') hv hx hy (hr z J' hJ')

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOfGen
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.KerPair

theorem exists_pow_gen {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ n := by
  induction n with
  | zero =>
    obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := fun k => ε k * (0 : ℕ))
      (fun U _ h => by simp) (LB.oneGen L (Y := Y))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨t', ht', fun Z r z J hJ => (hv _ _ z J hJ).trans ((val_one _).trans (pow_zero _).symm)⟩
  | succ n ih =>
    obtain ⟨s, hs, hv⟩ := ih
    obtain ⟨t', ht', hv'⟩ := exists_gen hL (φ' := φ) (ε' := fun k => ε k * (n + 1 : ℕ)) (fun U _ h => by
        refine (Fintype.prod_sum_type _).trans ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [← zpow_add]
        congr 1
        push_cast
        ring)
      (LB.mulGen L _ _ _ _ s t) (DVR.mulGen_isGen _ _ _ _ _ _ _ hs ht)
    refine ⟨t', ht', fun Z r z J hJ => (hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans ?_)⟩
    rw [hv Z r z J hJ, pow_succ]

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : RigLB B} (c : CubicalStr B L)
  {T : Over S} {x : T ⟶ B}

abbrev trφ (x : T ⟶ B) : Fin 2 → ((T ⊗ B).left ⟶ B.left) := ![((fst T B ≫ x) * snd T B).left, (snd T B).left]


omit [IsCommMonObj B] in
theorem prod_tr {T' : Over S} (ρ : T' ⟶ T) (b : T' ⟶ B) {U : Type} [CommGroup U] (h : (T'.left ⟶ B.left) → U) (m : ℤ) :
    ∏ k : Fin 2, h ((lift ρ b).left ≫ trφ x k) ^ ((![1, -1] : Fin 2 → ℤ) k * m) =
      h ((ρ ≫ x) * b).left ^ m * h b.left ^ (-m) := by
  have e₀ : (lift ρ b).left ≫ trφ x 0 = ((ρ ≫ x) * b).left := by
    show (lift ρ b ≫ ((fst T B ≫ x) * snd T B)).left = _
    rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]
  have e₁ : (lift ρ b).left ≫ trφ x 1 = b.left := by
    show (lift ρ b ≫ snd T B).left = _
    rw [lift_snd]
  rw [Fin.prod_univ_two, e₀, e₁]
  simp


omit [IsCommMonObj B] in
theorem prod_tr_one {T' : Over S} (ρ : T' ⟶ T) (b : T' ⟶ B) {U : Type} [CommGroup U] (h : (T'.left ⟶ B.left) → U) :
    ∏ k : Fin 2, h ((lift ρ b).left ≫ trφ x k) ^ (![1, -1] : Fin 2 → ℤ) k =
      h ((ρ ≫ x) * b).left * (h b.left)⁻¹ := by
  simpa using prod_tr (x := x) ρ b h 1

theorem val_mul_pt (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (u : LB.Gen (LB.LinComb L.L (trφ x) ![1, -1]))
    (hu : u.IsGen) (a b : T ⟶ B) (z : T.left) (J) (hJ : Good L.L z J) :
    val u (lift (𝟙 T) (a * b)).left z J * val u (lift (𝟙 T) (1 : T ⟶ B)).left z J =
      cubV c z J x a b * val u (lift (𝟙 T) a).left z J * val u (lift (𝟙 T) b).left z J := by
  let p := fst T B
  let q := snd T B
  let uu := fun w : T ⊗ B ⟶ B => LB.pullGen L.L _ _ u (lift p w).left
  have gu : ∀ w, (uu w).IsGen := fun w => DVR.pullGen_isGen _ _ _ _ hu _
  have vu : ∀ {T' : Over S} (σ : T' ⟶ T ⊗ B) {z : T'.left} {J}, Good L.L z J → ∀ w,
      val (uu w) σ.left z J = val u (lift (σ ≫ p) (σ ≫ w)).left z J := fun σ z J hJ w =>
    (val_pull hJ _ _ _).trans (by rw [← Over.comp_left, comp_lift])
  let t₁ := LB.mulGen L.L _ _ _ _ (uu ((p ≫ a) * q)) (uu 1)
  let t₂ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ B (x3 B)) thε c.t (lift (p ≫ x) (lift (p ≫ a) q)).left) (uu (p ≫ a))) (uu q)
  have ev : ∀ (w : T ⟶ B) {z : T.left} {J}, Good L.L z J →
      val t₁ (lift (𝟙 T) w).left z J =
        val u (lift (𝟙 T) (a * w)).left z J * val u (lift (𝟙 T) (1 : T ⟶ B)).left z J ∧
      val t₂ (lift (𝟙 T) w).left z J =
        cubV c z J x a w * val u (lift (𝟙 T) a).left z J * val u (lift (𝟙 T) w).left z J := fun w z J hJ => by
    have hp : lift (𝟙 T) w ≫ p = 𝟙 T := lift_fst _ _
    have hq : lift (𝟙 T) w ≫ q = w := lift_snd _ _
    have hp' : ∀ v : T ⟶ B, lift (𝟙 T) w ≫ p ≫ v = v := fun v => by rw [← Category.assoc, hp, Category.id_comp]
    constructor
    · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vu _ hJ _) (vu _ hJ _))).trans ?_
      rw [MonObj.comp_mul, MonObj.comp_one, hp, hq, hp']
    · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (val_cub c _ hJ _ _ _) (vu _ hJ _))) (vu _ hJ _))).trans ?_
      rw [hp, hq, hp', hp']
  refine (ev b hJ).1.symm.trans (Eq.trans ?_ (ev b hJ).2)
  refine gen_unique' L.isLB (fun V _ k => ?_) p.left (lift (𝟙 T) (1 : T ⟶ B)).left
    (by rw [← Over.comp_left, lift_fst, Over.id_left]) (WeilCube.surj_fst hG hB T)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gu _) (gu _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) (gu _)) (gu _))
    (fun y I hI => ?_) _ _ z J hJ
  · refine (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
      (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub (p ≫ x) (p ≫ a) q k) (prod_tr_one p (p ≫ a) k))
      (prod_tr_one p q k)).trans (Eq.trans ?_
      (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_tr_one p ((p ≫ a) * q) k) (prod_tr_one p 1 k)).symm)
    rw [_root_.mul_one, ← _root_.mul_assoc (p ≫ x)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · refine (ev 1 hI).1.trans (Eq.trans ?_ (ev 1 hI).2.symm)
    rw [_root_.mul_one, (isCub_cubV c (T := T) hI).face₃, _root_.one_mul]

theorem val_pow_pt (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (u : LB.Gen (LB.LinComb L.L (trφ x) ![1, -1]))
    (hu : u.IsGen) {N : ℕ} (hx : x ^ N = 1) (b : T ⟶ B) (z : T.left) (J) (hJ : Good L.L z J) :
    cubN (cubV c z J) N 1 x b * val u (lift (𝟙 T) b).left z J ^ N = val u (lift (𝟙 T) (1 : T ⟶ B)).left z J ^ N := by
  let p := fst T B
  let q := snd T B
  have hx' : (p ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨t, ht, hv⟩ := WeilCube.exists_gen_torsion c N (p ≫ x) q hx'
  obtain ⟨s, hs, hsv⟩ := exists_pow_gen L.isLB u hu N
  let uu := fun w : T ⊗ B ⟶ B => LB.pullGen L.L _ _ s (lift p w).left
  have gu : ∀ w, (uu w).IsGen := fun w => DVR.pullGen_isGen _ _ _ _ hs _
  have vu : ∀ {T' : Over S} (σ : T' ⟶ T ⊗ B) {z : T'.left} {J}, Good L.L z J → ∀ w,
      val (uu w) σ.left z J = val u (lift (σ ≫ p) (σ ≫ w)).left z J ^ N := fun σ z J hJ w =>
    (val_pull hJ _ _ _).trans ((hsv _ _ z J hJ).trans (by rw [← Over.comp_left, comp_lift]))
  let t₁ := LB.mulGen L.L _ _ _ _ t (uu q)
  have ev : ∀ (w : T ⟶ B) {z : T.left} {J}, Good L.L z J →
      val t₁ (lift (𝟙 T) w).left z J = cubN (cubV c z J) N 1 x w * val u (lift (𝟙 T) w).left z J ^ N ∧
      val (uu 1) (lift (𝟙 T) w).left z J = val u (lift (𝟙 T) (1 : T ⟶ B)).left z J ^ N := fun w z J hJ => by
    have hp : lift (𝟙 T) w ≫ p = 𝟙 T := lift_fst _ _
    have hq : lift (𝟙 T) w ≫ q = w := lift_snd _ _
    have hp' : ∀ v : T ⟶ B, lift (𝟙 T) w ≫ p ≫ v = v := fun v => by rw [← Category.assoc, hp, Category.id_comp]
    constructor
    · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ z J hJ) (vu _ hJ _))).trans ?_
      rw [hp, hq, hp']
    · refine (vu _ hJ _).trans ?_
      rw [MonObj.comp_one, hp]
  refine (ev b hJ).1.symm.trans (Eq.trans ?_ (ev b hJ).2)
  refine gen_unique' L.isLB (fun V _ k => ?_) p.left (lift (𝟙 T) (1 : T ⟶ B)).left
    (by rw [← Over.comp_left, lift_fst, Over.id_left]) (WeilCube.surj_fst hG hB T)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (gu _)) (gu _) (fun y I hI => ?_) _ _ z J hJ
  · refine (prod_tr p 1 k N).trans (Eq.trans ?_
      (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := V) _ rfl (prod_tr p q k N)).symm)
    rw [_root_.mul_one]
    simp only [Fin.prod_univ_succ, Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module
  · refine (ev 1 hI).1.trans (Eq.trans ?_ (ev 1 hI).2.symm)
    rw [(isCub_cubV c (T := T) hI).N_one, _root_.one_mul]

theorem cubWeil_of_gen : (GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (c : CubicalStr B L) (N : ℕ) (T : Over S) (x y : T ⟶ B), x ^ N = 1 → y ^ N = 1 → (∃ u : LB.Gen (translDiff B L.L x), u.IsGen) → CubWeil c N x y 1) := by
  intro hG S B _ _ hB L c N T x y hx hy ⟨u, hu⟩
  refine ⟨hx, hy, fun z J hJ => ?_⟩
  have C := isCub_cubV c hJ
  obtain ⟨U, hU⟩ : ∃ U : (T ⟶ B) → (T.left.presheaf.stalk z)ˣ,
      ∀ b, U b = val (L := L.L) (φ := trφ x) (ε := ![1, -1]) u (lift (𝟙 T) b).left z J := ⟨_, fun _ => rfl⟩
  have m : ∀ a b, U (a * b) * U 1 = cubV c z J x a b * U a * U b := fun a b => by
    simp only [hU]; exact val_mul_pt c hG hB u hu a b z J hJ
  have k : cubN (cubV c z J) N 1 x y * U y ^ N = U 1 ^ N := by
    simp only [hU]; exact val_pow_pt c hG hB u hu hx y z J hJ
  have b : ∀ n : ℕ, U (y ^ n) * U 1 ^ n = U 1 * (cubN (cubV c z J) n 1 y x * U y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have e := m (y ^ n) y
      rw [C.s01, C.s12] at e
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at e' ih' ⊢
      linear_combination (norm := abel) e' + ih'
  have b' := b N
  rw [hy] at b'
  rw [(gm (𝟙 T.left) z ⊤).map_one, _root_.one_mul]
  exact mul_right_cancel (k.trans (mul_left_cancel b'))

end GlobalTheory.UU.KerPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompRedIff
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.RingPoint

theorem toSpec_appTop {Z : Scheme.{0}} {D : Type} [CommRing D] (θ : D →+* Γ(Z, ⊤)) (a : Γ(Spec (CommRingCat.of D), ⊤)) :
    (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop.hom a = θ ((Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom a) := by
  have h : (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of D)).hom ≫ CommRingCat.ofHom θ := by
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom θ : CommRingCat.of D ⟶ Γ(Z, ⊤))
  exact congrArg (fun q => q.hom a) h

theorem exists_ringPoint {S : Scheme.{0}} (Y : Over S) [IsAffine Y.left] (D : Type) [CommRing D]
    (κ : Γ(Y.left, ⊤) →+* D) : ∃ (U : Over S) (y₀ : U ⟶ Y) (e : Γ(U.left, ⊤) ≃+* D), IsAffine U.left ∧
      (∀ b, e (y₀.left.appTop.hom b) = κ b) ∧
      ∀ (Z : Over S) (y : Z ⟶ Y) (θ : D →+* Γ(Z.left, ⊤)), (∀ b, θ (κ b) = y.left.appTop.hom b) →
        ∃ σ : Z ⟶ U, σ ≫ y₀ = y ∧ ∀ a, σ.left.appTop.hom a = θ (e a) := by
  let p : Spec (CommRingCat.of D) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom κ : Γ(Y.left, ⊤) ⟶ CommRingCat.of D) ≫ Y.left.isoSpec.inv
  have hp : ∀ b, (Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom (p.appTop.hom b) = κ b := fun b => by
    have h : p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom = CommRingCat.ofHom κ := by
      rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
      simp
    exact congrArg (fun q => q.hom b) h
  refine ⟨Over.mk (p ≫ Y.hom), Over.homMk p rfl, (Scheme.ΓSpecIso (CommRingCat.of D)).commRingCatIsoToRingEquiv,
    inferInstanceAs (IsAffine (Spec _)), hp, fun Z y θ hθ => ?_⟩
  have h : (Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) ≫ p = y.left := by
    refine ext_of_isAffine ?_
    ext b
    rw [Scheme.Hom.comp_appTop]
    exact (toSpec_appTop θ _).trans ((congrArg θ (hp b)).trans (hθ b))
  refine ⟨Over.homMk (Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) ?_, Over.OverMorphism.ext h, toSpec_appTop θ⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.hom) h).trans (Over.w y))

def strMap {A : Type} [CommRing A] (Z : Over (Spec (CommRingCat.of A))) : A →+* Γ(Z.left, ⊤) :=
  Z.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem appTop_strMap {A : Type} [CommRing A] {Z Y : Over (Spec (CommRingCat.of A))} (y : Z ⟶ Y) (a : A) :
    y.left.appTop.hom (strMap Y a) = strMap Z a := by
  rw [strMap, strMap, ← Over.w y, Scheme.Hom.comp_appTop]; rfl

theorem exists_comp_red_iff {A : Type} [CommRing A] (J : Ideal A) (Z : Over (Spec (CommRingCat.of A))) :
    (∃ s, s ≫ red J = Z.hom) ↔ ∀ a ∈ J, strMap Z a = 0 := by
  have nat : ∀ a, (red J).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ J))).inv.hom (Ideal.Quotient.mk J a) := fun a =>
    congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk J) : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ J))).symm
  constructor
  · rintro ⟨s, hs⟩ a ha
    rw [strMap, ← hs, Scheme.Hom.comp_appTop]
    change s.appTop.hom ((red J).appTop.hom _) = 0
    rw [nat, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero, map_zero]
  · intro h
    refine ⟨Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J (strMap Z) h)), ext_of_isAffine ?_⟩
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of A)).inv]
    ext a
    rw [Scheme.Hom.comp_appTop]
    refine (congrArg _ (nat a)).trans ((toSpec_appTop _ _).trans ?_)
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl

end GlobalTheory.UU.RingPoint
end
end

