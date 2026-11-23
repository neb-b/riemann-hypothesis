module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZeroOfIsAffineOpen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemBasicOpenIffGs
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.SectionRatio

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem mem_basicOpen_iff_gs {Y : Scheme.{0}} {U : Y.Opens} (f : Γ(Y, U)) (y : Y) (hy : y ∈ U) :
    y ∈ Y.basicOpen f ↔ IsUnit (gs (𝟙 Y) y U f) := by
  rw [gs_eq (𝟙 Y) y U hy f, Scheme.mem_basicOpen Y f y hy]
  exact Iff.rfl

theorem exists_quot {Y : Scheme.{0}} {U : Y.Opens} (a b : Γ(Y, U)) :
    ∃ q : Γ(Y, Y.basicOpen b), ∀ y ∈ Y.basicOpen b,
      gs (𝟙 Y) y _ q * gs (𝟙 Y) y U b = gs (𝟙 Y) y U a := by
  have hD : Y.basicOpen b ≤ U := Y.basicOpen_le b
  have hu : IsUnit ((Y.presheaf.map (homOfLE hD).op).hom b) := Y.toRingedSpace.isUnit_res_basicOpen b
  obtain ⟨w, hw⟩ := hu
  refine ⟨(Y.presheaf.map (homOfLE hD).op).hom a * ↑w⁻¹, fun y hy => ?_⟩
  have key : ((Y.presheaf.map (homOfLE hD).op).hom a * ↑w⁻¹) * (Y.presheaf.map (homOfLE hD).op).hom b =
      (Y.presheaf.map (homOfLE hD).op).hom a := by
    have hw' : (Y.presheaf.map (homOfLE hD).op).hom b = ↑w := hw.symm
    rw [hw', _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
  rw [← gs_res (𝟙 Y) y hD hy b, ← gs_mul (𝟙 Y) y _ hy, key, gs_res (𝟙 Y) y hD hy a]

private theorem exists_global_unit_of_compatible_of_iSup_eq {Y : Scheme.{0}} {P : Type} (W : P → Y.Opens) (hW : ∀ y, ∃ p, y ∈ W p)
    (q : ∀ p, Γ(Y, W p))
    (hq : ∀ p p' (y : Y), y ∈ W p → y ∈ W p' → gs (𝟙 Y) y (W p) (q p) = gs (𝟙 Y) y (W p') (q p')) :
    ∃ c : Γ(Y, ⊤), ∀ p (y : Y), y ∈ W p → gs (𝟙 Y) y ⊤ c = gs (𝟙 Y) y (W p) (q p) := by
  have hcov : (⊤ : Y.Opens) ≤ iSup W := fun y _ => by
    obtain ⟨p, hp⟩ := hW y
    exact Opens.mem_iSup.2 ⟨p, hp⟩
  have hcomp : TopCat.Presheaf.IsCompatible Y.sheaf.1 W q := by
    intro p p'
    apply fn_ext
    intro y hy
    exact (gs_res (𝟙 Y) y inf_le_left hy (q p)).trans
      ((hq p p' y hy.1 hy.2).trans (gs_res (𝟙 Y) y inf_le_right hy (q p')).symm)
  obtain ⟨c, hc, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf W ⊤ (fun p => homOfLE le_top) hcov q hcomp
  refine ⟨c, fun p y hy => ?_⟩
  rw [← hc p]
  exact (gs_res (𝟙 Y) y le_top hy c).symm

private theorem gs_id_linComb_eq_trF_mul_sval {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (j : K → L.ι) (y : Y) (hy : y ∈ (LB.LinComb L φ ε).U j)
    (J : (Y ⟶ X) → L.ι) (hJ : Good L y J) :
    gs (𝟙 Y) y ((LB.LinComb L φ ε).U j) (s.f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval s (𝟙 Y) y J :=
  sec_trans s (𝟙 Y) y hy (hJ.mem φ (𝟙 Y))

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {Ix : Type} (a b : Ix → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ (y : Y) (J), Good L y J → ∃ i, IsUnit (sval (b i) (𝟙 Y) y J))
    (hab : ∀ i i' (y : Y) (J), Good L y J →
      sval (a i) (𝟙 Y) y J * sval (b i') (𝟙 Y) y J = sval (a i') (𝟙 Y) y J * sval (b i) (𝟙 Y) y J) :
    ∃ c : Γ(Y, ⊤), ∀ i (y : Y) (J), Good L y J →
      sval (a i) (𝟙 Y) y J = gs (𝟙 Y) y ⊤ c * sval (b i) (𝟙 Y) y J := by

  let W : Ix × (K → L.ι) → Y.Opens := fun p => Y.basicOpen ((b p.1).f p.2)
  choose q hq using fun p : Ix × (K → L.ι) => exists_quot ((a p.1).f p.2) ((b p.1).f p.2)
  have goodAt : ∀ y : Y, ∃ J, Good L y J := fun y => by
    obtain ⟨J, hJ, -⟩ := exists_good L hL y (K := Empty) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim)
    exact ⟨J, hJ⟩

  have loc : ∀ p (y : Y), y ∈ W p → ∀ J, Good L y J →
      gs (𝟙 Y) y (W p) (q p) * sval (b p.1) (𝟙 Y) y J = sval (a p.1) (𝟙 Y) y J ∧
        IsUnit (sval (b p.1) (𝟙 Y) y J) := by
    intro p y hy J hJ
    have hyc : y ∈ (LB.LinComb L φ ε).U p.2 := Y.basicOpen_le _ hy
    have e := hq p y hy
    rw [gs_id_linComb_eq_trF_mul_sval (b p.1) p.2 y hyc J hJ, gs_id_linComb_eq_trF_mul_sval (a p.1) p.2 y hyc J hJ] at e
    have hu := (mem_basicOpen_iff_gs ((b p.1).f p.2) y hyc).1 hy
    rw [gs_id_linComb_eq_trF_mul_sval (b p.1) p.2 y hyc J hJ] at hu
    set T := trF φ ε (𝟙 Y) y p.2 (fun k => J (𝟙 Y ≫ φ k))
    refine ⟨?_, isUnit_of_mul_isUnit_right hu⟩
    apply T.isUnit.mul_left_cancel
    linear_combination e
  obtain ⟨c, hc⟩ := exists_global_unit_of_compatible_of_iSup_eq W (fun y => by
      obtain ⟨J, hJ⟩ := goodAt y
      obtain ⟨i, hi⟩ := hb y J hJ
      exact ⟨(i, fun k => J (𝟙 Y ≫ φ k)),
        (mem_basicOpen_iff_gs ((b i).f _) y (hJ.mem φ (𝟙 Y))).2 hi⟩) q
    (fun p p' y hy hy' => by
      obtain ⟨J, hJ⟩ := goodAt y
      obtain ⟨e1, u1⟩ := loc p y hy J hJ
      obtain ⟨e2, u2⟩ := loc p' y hy' J hJ
      have e3 := hab p.1 p'.1 y J hJ
      apply (u1.mul u2).mul_right_cancel
      linear_combination sval (b p'.1) (𝟙 Y) y J * e1 + e3 - sval (b p.1) (𝟙 Y) y J * e2)
  refine ⟨c, fun i y J hJ => ?_⟩
  obtain ⟨i₀, h₀⟩ := hb y J hJ
  have hy₀ : y ∈ W (i₀, fun k => J (𝟙 Y ≫ φ k)) :=
    (mem_basicOpen_iff_gs ((b i₀).f _) y (hJ.mem φ (𝟙 Y))).2 h₀
  obtain ⟨e1, -⟩ := loc _ y hy₀ J hJ
  rw [hc _ y hy₀]
  apply h₀.mul_right_cancel
  linear_combination hab i i₀ y J hJ - sval (b i) (𝟙 Y) y J * e1

theorem ratio_glue : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ K₃ : Type) [Fintype K₁] [Fintype K₂] [Fintype K₃] (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (φ₃ : K₃ → (Y ⟶ X)) (ε₃ : K₃ → ℤ) (h : Y ⟶ Y), Geo.Tor.FormEq φ₁ ε₁ (Sum.elim (fun k => h ≫ φ₂ k) φ₃) (Sum.elim ε₂ ε₃) → ∀ (u : LB.Gen (LB.LinComb L φ₃ ε₃)), u.IsGen → ∀ (Ix : Type) (s'' : Ix → LB.Sec (LB.LinComb L φ₁ ε₁)) (s : Ix → LB.Sec (LB.LinComb L φ₂ ε₂)), (∀ (y : Y) (J), Geo.Tor.Good L y J → ∃ i, IsUnit (Geo.Tor.sval (s i) h y J)) → (∀ i i' (y : Y) (J), Geo.Tor.Good L y J → Geo.Tor.sval (s'' i) (𝟙 Y) y J * Geo.Tor.sval (s i') h y J = Geo.Tor.sval (s'' i') (𝟙 Y) y J * Geo.Tor.sval (s i) h y J) → ∃ c : Γ(Y, ⊤), ∀ i (y : Y) (J), Geo.Tor.Good L y J → Geo.Tor.sval (s'' i) (𝟙 Y) y J = Geo.Tor.gs (𝟙 Y) y ⊤ c * (Geo.Tor.sval (s i) h y J * (Geo.Tor.val u (𝟙 Y) y J).val) := by
  intro X Y L hL K₁ K₂ K₃ _ _ _ φ₁ ε₁ φ₂ ε₂ φ₃ ε₃ h hF u hu Ix s'' s hs hx
  have hF' : Geo.Tor.FormEq (Sum.elim (fun k => h ≫ φ₂ k) φ₃) (Sum.elim ε₂ ε₃) φ₁ ε₁ :=
    fun U _ g => (hF U g).symm
  choose b hb using fun i => Geo.Tor.exists_sec hL hF' (Geo.Tor.pullMulSec (s i) h u hu)
  have key : ∀ i (y : Y) (J), Geo.Tor.Good L y J →
      Geo.Tor.sval (b i) (𝟙 Y) y J = Geo.Tor.sval (s i) h y J * (Geo.Tor.val u (𝟙 Y) y J).val := by
    intro i y J hJ
    rw [hb i Y (𝟙 Y) y J hJ, Geo.Tor.sval_pullMulSec (s i) h u hu (𝟙 Y) y hJ, Category.id_comp]
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.SectionRatio.exists_ratio hL s'' b
    (fun y J hJ => by
      obtain ⟨i, hi⟩ := hs y J hJ
      exact ⟨i, by rw [key i y J hJ]; exact hi.mul (Geo.Tor.val u (𝟙 Y) y J).isUnit⟩)
    (fun i i' y J hJ => by
      rw [key i y J hJ, key i' y J hJ]
      linear_combination (Geo.Tor.val u (𝟙 Y) y J).val * hx i i' y J hJ)
  refine ⟨c, fun i y J hJ => ?_⟩
  rw [hc i y J hJ, key i y J hJ]

end GlobalTheory.SectionRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecEqOfThick
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.MixedCross

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cross_pow {Γ : Type} [CommRing Γ] (W W' X : Γˣ) {k₁ k₂ m₁ m₂ N : ℕ} (hm : m₁ * k₁ = m₂ * k₂)
    (s₁ t₁ s₂ t₂ : Γ)
    (h₁ : (W ^ (k₁ * N)).val * s₁ = (X ^ k₁).val * ((W' ^ k₁).val * t₁))
    (h₂ : (W ^ (k₂ * N)).val * s₂ = (X ^ k₂).val * ((W' ^ k₂).val * t₂)) :
    s₁ ^ m₁ * t₂ ^ m₂ = s₂ ^ m₂ * t₁ ^ m₁ := by
  push_cast at h₁ h₂
  have e₁ := congrArg (· ^ m₁) h₁
  have e₂ := congrArg (· ^ m₂) h₂
  simp only [mul_pow, ← pow_mul] at e₁ e₂
  have a₁ : k₁ * N * m₁ = m₁ * k₁ * N := by ring
  have a₂ : k₂ * N * m₂ = m₁ * k₁ * N := by rw [hm]; ring
  have b₁ : k₁ * m₁ = m₁ * k₁ := by ring
  have b₂ : k₂ * m₂ = m₁ * k₁ := by rw [hm]; ring
  rw [a₁, b₁] at e₁
  rw [a₂, b₂] at e₂
  have hu : IsUnit ((W : Γ) ^ (m₁ * k₁ * N)) := W.isUnit.pow _
  apply hu.mul_left_cancel
  calc (W : Γ) ^ (m₁ * k₁ * N) * (s₁ ^ m₁ * t₂ ^ m₂)
      = ((W : Γ) ^ (m₁ * k₁ * N) * s₁ ^ m₁) * t₂ ^ m₂ := by ring
    _ = (X : Γ) ^ (m₁ * k₁) * ((W' : Γ) ^ (m₁ * k₁) * t₁ ^ m₁) * t₂ ^ m₂ := by rw [e₁]
    _ = ((W : Γ) ^ (m₁ * k₁ * N) * s₂ ^ m₂) * t₁ ^ m₁ := by rw [e₂]; ring
    _ = (W : Γ) ^ (m₁ * k₁ * N) * (s₂ ^ m₂ * t₁ ^ m₁) := by ring

theorem gs_sub' {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by
  simp only [gs, dif_pos h, map_sub]

theorem sec_eq_of_thick (hB : lemmaBSt.{0}) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (G.left ⟶ Y)} {ε : K → ℤ}
    (s s' : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ (e : ℕ) (z : (thickObj V (maximalIdeal V) e G).left) (J), Good L z J →
      sval s (fGl (maximalIdeal V) G e) z J = sval s' (fGl (maximalIdeal V) G e) z J) (j : K → L.ι) :
    s.f j = s'.f j := by
  classical
  unfold sval fGl at h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hN : (LB.LinComb L φ ε).IsLB := linComb_isLB L hL φ ε
  refine sub_eq_zero.mp (hB V G (LB.LinComb L φ ε) hN (subSec s s') ϖ hϖ (fun i e => ?_) j)
  cases e with
  | zero => simp
  | succ e =>
    have hv : ∀ i', ((fstG (maximalIdeal V) e G).left.app ((LB.LinComb L φ ε).U i')).hom
        ((subSec s s').f i') = 0 := by
      intro i'
      apply fn_ext
      intro z hz
      have hz' : (fstG (maximalIdeal V) e G).left z ∈ LB.wchart L φ i' := hz
      obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
      have hm := hJ.mem φ (fstG (maximalIdeal V) e G).left
      have h1 := h e z J hJ
      rw [gs_eq (𝟙 _) z _ hz 0, map_zero, map_zero, gs_pull (𝟙 _) _ z ((LB.LinComb L φ ε).U i') hz', Category.id_comp]
      show gs (fstG (maximalIdeal V) e G).left z (LB.wchart L φ i') (s.f i' - s'.f i') = 0
      refine (gs_sub' _ z (LB.wchart L φ i') hz' (s.f i') (s'.f i')).trans (sub_eq_zero.mpr ?_)
      rw [sec_trans s _ z hz' hm, sec_trans s' _ z hz' hm, h1]
    obtain ⟨τ, hτ⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G (LB.LinComb L φ ε) (subSec s s') e).1 hv
    unfold SecIsMul at hτ
    rw [hτ i]
    refine Ideal.mul_mem_right _ _ ?_
    have hc : resTop ((LB.LinComb L φ ε).U i) (scal G.hom (ϖ ^ (e + 1))) =
        ((G.left.presheaf.map (homOfLE le_top).op).hom
          ((G.hom.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ϖ))) ^ (e + 1) := by
      simp only [resTop, scal, map_pow]
      rfl
    rw [hc]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _

theorem main : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (k₁ k₂ m₁ m₂ : ℕ), m₁ * k₁ = m₂ * k₂ → ∀ (σ₁ : H0 P.U.LG.L (k₁ * N)) (τ₁ : H0 P.U.LG.L k₁) (σ₂ : H0 P.U.LG.L (k₂ * N)) (τ₂ : H0 P.U.LG.L k₂), (∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k₁ * N)).val * sv P.U.toUnifPre (k₁ * N) σ₁ (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k₁).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k₁).val * sv P.U.toUnifPre k₁ τ₁ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL'))) → (∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k₂ * N)).val * sv P.U.toUnifPre (k₂ * N) σ₂ (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k₂).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k₂).val * sv P.U.toUnifPre k₂ τ₂ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (y : Z) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval σ₁ r y J ^ m₁ * Geo.Tor.sval τ₂ (r ≫ (t.act.act a).left) y J ^ m₂ = Geo.Tor.sval σ₂ r y J ^ m₂ * Geo.Tor.sval τ₁ (r ≫ (t.act.act a).left) y J ^ m₁ := by
  intro hB V _ _ _ E _ _ _ H t P a N haN hN X k₁ k₂ m₁ m₂ hm σ₁ τ₁ σ₂ τ₂ h₁ h₂
  classical
  have : Smooth t.G.hom := t.semi.smooth
  have : IsSeparated t.G.hom := t.semi.separated
  have : QuasiCompact t.G.hom := t.semi.quasiCompact
  have : GeometricallyConnected t.G.hom := t.semi.geomConnected
  have hL : P.U.LG.L.IsLB := P.U.LG.isLB
  have hD : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  have eA : ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (y : Z) (J : (Z ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L y J →
      sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => σ₁)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => τ₂)) (t.act.act a).left)) r y J = sval σ₁ r y J ^ m₁ * sval τ₂ (r ≫ (t.act.act a).left) y J ^ m₂ := by
    intro Z r y J hJ
    rw [H1.SectionArithmetic.sval_mulSec _ _ r y hJ, H1.SectionArithmetic.sval_pullSec _ _ r y hJ, H1.SectionArithmetic.sval_powSec _ r y hJ,
      H1.SectionArithmetic.sval_powSec _ _ y hJ]
    simp [Finset.prod_const]
  have eB : ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (y : Z) (J : (Z ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L y J →
      sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => σ₂)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => τ₁)) (t.act.act a).left)) r y J = sval σ₂ r y J ^ m₂ * sval τ₁ (r ≫ (t.act.act a).left) y J ^ m₁ := by
    intro Z r y J hJ
    rw [H1.SectionArithmetic.sval_mulSec _ _ r y hJ, H1.SectionArithmetic.sval_pullSec _ _ r y hJ, H1.SectionArithmetic.sval_powSec _ r y hJ,
      H1.SectionArithmetic.sval_powSec _ _ y hJ]
    simp [Finset.prod_const]
  obtain ⟨B', hB'⟩ : ∃ B' : type_of% (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => σ₁)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => τ₂)) (t.act.act a).left)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (J : (Z ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L z J →
        sval B' r z J = sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => σ₂)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => τ₁)) (t.act.act a).left)) r z J := by
    refine exists_sec hL ?_ _
    intro U _ h
    simp only [Fintype.prod_sum_type, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Sum.elim_inl, Sum.elim_inr, Category.comp_id]
    have hz : (m₁ : ℤ) * k₁ = m₂ * k₂ := by exact_mod_cast hm
    simp only [← zpow_natCast, ← zpow_mul]
    congr 2
    · push_cast
      linear_combination (-(N : ℤ)) * hz
    · push_cast
      linear_combination hz
  have hthick : ∀ (e : ℕ) (z : (thickObj V (maximalIdeal V) e t.G).left)
      (J : ((thickObj V (maximalIdeal V) e t.G).left ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L z J →
      sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => σ₁)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => τ₂)) (t.act.act a).left)) (fGl (maximalIdeal V) t.G e) z J = sval B' (fGl (maximalIdeal V) t.G e) z J := by
    intro e z J hJ
    rw [hB' _ _ z J hJ, eA _ _ z J hJ, eB _ _ z J hJ]
    obtain ⟨JD, hJD, -⟩ := exists_good P.D.toPre.P.L hD z (K := Empty) Empty.elim Empty.elim
      (fun a => a.elim) (fun a => a.elim)
    have m1 : (𝟙 _ ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U (J (fGl (maximalIdeal V) t.G e ≫ 𝟙 t.G.left)) := by
      simpa using hJ (fGl (maximalIdeal V) t.G e ≫ 𝟙 t.G.left)
    have m2 : ((𝟙 _ ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫
        fGl (maximalIdeal V) t.G e) z ∈
          P.U.LG.L.U (J ((fGl (maximalIdeal V) t.G e ≫ (t.act.act a).left) ≫ 𝟙 t.G.left)) := by
      have hz := hJ ((fGl (maximalIdeal V) t.G e ≫ (t.act.act a).left) ≫ 𝟙 t.G.left)
      have eq : (𝟙 _ ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫
          fGl (maximalIdeal V) t.G e = (fGl (maximalIdeal V) t.G e ≫ (t.act.act a).left) ≫ 𝟙 t.G.left := by
        rw [Category.id_comp, Category.comp_id]
        exact fstG_act _ _ _
      rw [eq]
      exact hz
    have c := cross_pow _ _ _ hm _ _ _ _ (h₁ e _ (𝟙 _) z JD hJD _ _ m1 m2) (h₂ e _ (𝟙 _) z JD hJD _ _ m1 m2)
    unfold sv at c
    simp only [Category.id_comp, fGl, fstG_act] at c
    unfold sval
    simp only [fGl]
    exact c
  intro Z r y J hJ
  rw [← eA Z r y J hJ, ← eB Z r y J hJ, ← hB' Z r y J hJ]
  have hAB := sec_eq_of_thick hB t.G hL _ B' hthick
  unfold sval
  rw [hAB]

end GlobalTheory.MixedCross
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitValue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

lemma eSec_pullback_fst {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    eSec ((Over.pullback p).obj G) ≫ pullback.fst G.hom p = p ≫ eSec G := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

lemma krull_ext {V : Type} [CommRing V] [IsNoetherianRing V] [IsLocalRing V]
    (W : (Spec (CommRingCat.of V)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of V), W))
    (h : ∀ (e : ℕ) (z), gs (thick V (maximalIdeal V) e) z W a = gs (thick V (maximalIdeal V) e) z W b) :
    a = b := by
  subst hW
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).hom).1
  apply hinj
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top, Ideal.mem_iInf]
  intro e
  refine Ideal.pow_le_pow_right (Nat.le_succ e) (Ideal.Quotient.eq.1 ?_)
  have key : ((thick V (maximalIdeal V) e).app ⊤).hom a = ((thick V (maximalIdeal V) e).app ⊤).hom b := by
    refine fn_ext fun z hz => ?_
    rw [gs_pull _ _ z ⊤ trivial, gs_pull _ _ z ⊤ trivial, Category.id_comp]
    exact h e z
  have nat := fun x => congrArg (fun φ => φ.hom x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  exact (nat a).symm.trans ((congrArg _ key).trans (nat b))

lemma trF_unique {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] [Unique K] (φ : Y ⟶ X) (n : ℤ) (r : Z ⟶ Y)
    (z : Z) (J : (Z ⟶ X) → L.ι) (j : L.ι) (q : Z ⟶ X) (hq : r ≫ φ = q) :
    trF (L := L) (fun _ : K => φ) (fun _ => n) r z (fun _ => J (r ≫ φ)) (fun _ => j) =
      gm q z (L.U (J q) ⊓ L.U j) (L.g (J q) j) ^ n := by
  subst hq
  exact Fintype.prod_unique _

def thU (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) :
    (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
  thick R I e

section Thick

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ)

lemma eSec_fGl : eSec (thickObj R I e G) ≫ fGl I G e = thU R I e ≫ eSec G :=
  eSec_pullback_fst _ _

lemma eSec_pGl : eSec (thickObj R I e G) ≫ pGl U e = thU R I e ≫ eSec D.toPre.P.A := by
  have := (U.gt e).q_hom
  have h1 : (η[thickObj R I e G] ≫ (U.gt e).q) = η[thickObj R I e D.toPre.P.A] := IsMonHom.one_hom _
  have h2 : eSec (thickObj R I e G) ≫ (U.gt e).q.left = eSec (thickObj R I e D.toPre.P.A) :=
    congrArg Over.Hom.left h1
  refine Eq.trans ?_ (eSec_pullback_fst (thick R I e) _)
  rw [← h2, Category.assoc]
  rfl

lemma eSec_map (f : G ⟶ G) [IsMonHom f] :
    eSec (thickObj R I e G) ≫ ((Over.pullback (thick R I e)).map f).left = eSec (thickObj R I e G) :=
  congrArg Over.Hom.left (IsMonHom.one_hom ((Over.pullback (thick R I e)).map f))

lemma wv_rig (z : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
    (hM : (thU R I e ≫ eSec D.toPre.P.A) z ∈ D.toPre.P.L.U jM) (hL : (thU R I e ≫ eSec G) z ∈ U.LG.L.U jL) :
    wv U e (eSec (thickObj R I e G)) z jM jL *
      gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => jL)) (U.LG.rig.s (fun _ => jL)) =
      gm (thU R I e) z ((D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM)) (D.toPre.rig.s (fun _ => jM)) := by
  have m₁ : z ∈ eSec (thickObj R I e G) ⁻¹ᵁ ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL)) :=
    ⟨mem_pull.2 ((congrArg (fun g => g z ∈ D.toPre.P.L.U jM) (eSec_pGl U e)).mpr hM),
      mem_pull.2 ((congrArg (fun g => g z ∈ U.LG.L.U jL) (eSec_fGl (G := G) e)).mpr hL)⟩
  have m₂ : z ∈ thU R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => jL) := mem_pull.2 hL
  have m₃ : z ∈ thU R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM) := mem_pull.2 hM
  have hz : z ∈ (eSec (thickObj R I e G) ⁻¹ᵁ ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL))) ⊓ thU R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => jL) ⊓
      thU R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM) := ⟨⟨m₁, m₂⟩, m₃⟩
  have W := congrArg (gm (𝟙 _) z _) (U.w_rig e (fun _ => jM, fun _ => jL) _
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ _ z _ _ _ hz _) (gm_rp₁ _ z _ _ _ hz _))).symm.trans
    (W.trans (gm_rp₁ _ z _ _ _ hz _))

lemma unit_value_thick (f : G ⟶ G) [IsMonHom f] {g : D.toPre.P.A.left ⟶ D.toPre.P.A.left} {N : ℕ} (hN : 0 < N)
    {ε : Fin 2 → ℤ} (X : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, g] ε))
    (hX : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (eSec D.toPre.P.A))
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (1 * (N - 1))))
    (k : ℕ) (σ'' : H0 U.LG.L (k * N)) (τ : H0 U.LG.L k)
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J → ∀ jL jL',
      (r ≫ fGl I G e) z ∈ U.LG.L.U jL →
      ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ fGl I G e) z ∈ U.LG.L.U jL' →
      (wv U e r z (J (r ≫ pGl U e)) jL ^ (k * N)).val * sv U (k * N) σ'' (r ≫ fGl I G e) z jL =
        (val X (r ≫ pGl U e) z J ^ k).val *
          ((wv U e (r ≫ ((Over.pullback (thick R I e)).map f).left) z
            (J ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ pGl U e)) jL' ^ k).val *
            sv U k τ ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ fGl I G e) z jL'))
    (z : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left) (j : U.LG.L.ι)
    (hj : (thU R I e ≫ eSec G) z ∈ U.LG.L.U j) :
    sv U (k * N) σ'' (thU R I e ≫ eSec G) z j =
      (gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => j)) (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        sv U k τ (thU R I e ≫ eSec G) z j := by
  choose J hJ using fun ψ : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left ⟶ D.toPre.P.A.left =>
    exists_chart D.toPre.P.isLB (ψ z)
  have hJ : Good D.toPre.P.L z J := hJ
  have E := H _ (eSec (thickObj R I e G)) z J hJ j j (by rw [eSec_fGl]; exact hj)
    (by rw [eSec_map, eSec_fGl]; exact hj)
  rw [eSec_map, eSec_fGl, eSec_pGl] at E
  have hw := wv_rig U e z _ j (hJ (thU R I e ≫ eSec D.toPre.P.A)) hj
  have hx : val X (thU R I e ≫ eSec D.toPre.P.A) z J =
      gm (thU R I e) z ((D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => J (thU R I e ≫ eSec D.toPre.P.A)))
        (D.toPre.rig.s (fun _ => J (thU R I e ≫ eSec D.toPre.P.A))) ^ (1 * (N - 1)) :=
    (val_pull hJ X _ _).symm.trans ((val_corr hJ hX _).trans (map_pow _ _ _))
  rw [hx, ← hw] at E
  generalize wv U e (eSec (thickObj R I e G)) z (J (thU R I e ≫ eSec D.toPre.P.A)) j = w at E
  generalize gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => j)) (U.LG.rig.s (fun _ => j)) = u at E ⊢
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  refine (w ^ (k * (n + 1))).mul_right_inj.1 (E.trans ?_)
  simp only [Nat.add_sub_cancel, Units.val_pow_eq_pow_val, Units.val_mul]
  ring

end Thick

theorem unit_value {V : Type} [CommRing V] [IsDomain V] [IsNoetherianRing V] [IsLocalRing V]
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
    {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    (U : UnifPre (maximalIdeal V) D A G) {N : ℕ} (hN : 0 < N) (k : ℕ) (σ'' : H0 U.LG.L (k * N)) (τ : H0 U.LG.L k)
    (H : ∀ (e : ℕ) (z) (j : U.LG.L.ι), (thU V (maximalIdeal V) e ≫ eSec G) z ∈ U.LG.L.U j →
      sv U (k * N) σ'' (thU V (maximalIdeal V) e ≫ eSec G) z j =
      (gm (thU V (maximalIdeal V) e) z ((U.LG.L.pull (eSec G)).U (fun _ => j))
        (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val * sv U k τ (thU V (maximalIdeal V) e ≫ eSec G) z j)
    (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (J) (hJ : Good U.LG.L y J) :
    sval σ'' (r ≫ eSec G) y J =
      (val (L := U.LG.L) U.LG.rig r y J ^ (k * (N - 1))).val * sval τ (r ≫ eSec G) y J := by
  obtain ⟨j, hj⟩ := exists_chart U.LG.isLB (eSec G (IsLocalRing.closedPoint V))
  have hj' : ∀ x, eSec G x ∈ U.LG.L.U j := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := V) x).map (eSec G).continuous).mem_open (U.LG.L.U j).isOpen hj
  let W₁ : G.left.Opens := LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j)
  have m₁ : ∀ x, eSec G x ∈ W₁ := fun x => Set.mem_iInter.2 fun _ => hj' x
  let W : (𝟙_ (Over (Spec (CommRingCat.of V)))).left.Opens := (U.LG.L.pull (eSec G)).U (fun _ => j)
  have m : ∀ x, x ∈ W := fun x => mem_pull.2 (hj' x)
  have hle : W ≤ eSec G ⁻¹ᵁ W₁ := fun x _ => m₁ x
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (s : Γ(G.left, W₁)),
      gs r y W (rs hle (((eSec G).app W₁).hom s)) = gs (r ≫ eSec G) y W₁ s := fun Z r y s =>
    (gs_res r y hle (m _) _).trans (gs_pull r (eSec G) y W₁ (m₁ _) s)
  have ev' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z),
      gs r y W ((@id Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, W)ˣ (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        rs hle (((eSec G).app W₁).hom (τ.f (fun _ => j)))) =
      (gm r y W (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val * sv U k τ (r ≫ eSec G) y j := fun Z r y =>
    (gs_mul r y W (m _) _ _).trans (congrArg₂ (· * ·) ((gs_unit r y W (m _) _).trans
      (congrArg Units.val (map_pow _ _ _))) (ev Z r y _))
  have key : rs hle (((eSec G).app W₁).hom (σ''.f (fun _ => j))) =
      (@id Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, W)ˣ (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        rs hle (((eSec G).app W₁).hom (τ.f (fun _ => j))) :=
    krull_ext W (eq_top_iff.2 fun x _ => m x) _ _ fun e z =>
      (ev _ (thU V (maximalIdeal V) e) z _).trans ((H e z j (hj' _)).trans (ev' _ (thU V (maximalIdeal V) e) z).symm)
  have E := (ev Z r y _).symm.trans ((congrArg (gs r y W) key).trans (ev' Z r y))
  have a₁ : sval σ'' (r ≫ eSec G) y J = _ :=
    sec_trans σ'' (r ≫ eSec G) y (hJ.mem _ (r ≫ eSec G)) (j' := fun _ => j) (m₁ _)
  have a₂ : sval τ (r ≫ eSec G) y J = _ :=
    sec_trans τ (r ≫ eSec G) y (hJ.mem _ (r ≫ eSec G)) (j' := fun _ => j) (m₁ _)
  have a₃ : val (L := U.LG.L) U.LG.rig r y J = _ :=
    gen_trans (L := U.LG.L) U.LG.rigGen r y (hJ.mem _ r) (j' := fun _ => j) (m _)
  rw [a₁, a₂, a₃]
  refine (congrArg _ E).trans ?_
  rw [trF_unique _ _ _ _ J j (r ≫ eSec G) (Category.comp_id _), trF_unique _ _ _ _ J j (r ≫ eSec G) (Category.comp_id _),
    trF_unique _ _ _ _ J j (r ≫ eSec G) rfl]
  simp only [zpow_natCast, zpow_one]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have alg : ∀ (c u : (Z.presheaf.stalk y)ˣ) (s : Z.presheaf.stalk y), (c ^ (k * (n + 1))).val * ((u ^ (k * n)).val * s) =
      ((c * u) ^ (k * n)).val * ((c ^ k).val * s) := fun c u s => by
    simp only [Units.val_pow_eq_pow_val, Units.val_mul]
    ring
  exact alg _ _ _

theorem value_at_unit_section : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])), X.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ X (eSec P.D.toPre.P.A)) (GeneratorPullback.powGen P.D.toPre.P.L _ _ P.D.toPre.rig (1 * (N - 1))) → ∀ (k : ℕ) (σ'' : H0 P.U.LG.L (k * N)) (τ : H0 P.U.LG.L k), (∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k * N)).val * sv P.U.toUnifPre (k * N) σ'' (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k).val * sv P.U.toUnifPre k τ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval σ'' (r ≫ eSec t.G) y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig r y J ^ (k * (N - 1))).val * Geo.Tor.sval τ (r ≫ eSec t.G) y J := by
  intro V _ _ _ E _ _ _ H t P a N _ hN X _ hX k σ'' τ h
  have := t.act.hom a
  exact unit_value P.U.toUnifPre hN k σ'' τ fun e => unit_value_thick P.U.toUnifPre e (t.act.act a) hN X hX k σ'' τ (h e)

end GlobalTheory.UnitValue
end
end

