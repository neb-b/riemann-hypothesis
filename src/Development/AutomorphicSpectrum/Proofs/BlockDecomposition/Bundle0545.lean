module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdZpowSingle
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.TwUnits

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (h'' : W ≤ U) (x : Γ(X, U)ˣ) :
    Semi.res h' (Semi.res h x) = Semi.res h'' x := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom x.val) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_div_g {X : Scheme.{0}} (T L : LB X) (p q : T.ι × L.ι) {W : X.Opens}
    (h : W ≤ (T.U p.1 ⊓ L.U p.2) ⊓ (T.U q.1 ⊓ L.U q.2)) (h₁ : W ≤ T.U p.1 ⊓ T.U q.1) (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    Semi.res h ((LB.div T L).g p q) = Semi.res h₁ (T.g p.1 q.1) * (Semi.res h₂ (L.g p.2 q.2))⁻¹ :=
  (map_mul (Semi.res h) _ _).trans (congrArg₂ (· * ·) (res_res' _ _ h₁ _)
    ((map_inv (Semi.res h) _).trans (congrArg (·⁻¹) (res_res' _ _ h₂ _))))

theorem iso_law {X : Scheme.{0}} {L T : LB X} {w : LB.Iso L T} (hw : w.IsGen) (p q : T.ι × L.ι) {W : X.Opens}
    (hp : W ≤ T.U p.1 ⊓ L.U p.2) (hq : W ≤ T.U q.1 ⊓ L.U q.2) (h₁ : W ≤ T.U p.1 ⊓ T.U q.1)
    (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    Semi.res hp (w.s p) = Semi.res h₁ (T.g p.1 q.1) * (Semi.res h₂ (L.g p.2 q.2))⁻¹ * Semi.res hq (w.s q) := by
  have e := congrArg (Semi.res (le_inf hp hq)) (hw p q)
  exact ((res_res' _ _ hp _).symm.trans e).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (res_div_g T L p q (le_inf hp hq) h₁ h₂) (res_res' _ _ hq _)))

theorem res_pull_g (k : Fin (m + 1)) (j j' : PUnit → Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ ((O1 ℤ (n k)).pull (pr ℤ m n k)).U j ⊓ ((O1 ℤ (n k)).pull (pr ℤ m n k)).U j')
    (h' : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (j PUnit.unit) ⊓ chart ℤ (n k) (j' PUnit.unit))) :
    Semi.res h (((O1 ℤ (n k)).pull (pr ℤ m n k)).g j j') = blockUnit (j PUnit.unit) (j' PUnit.unit) h' := by
  have e := linComb_punit_g (O1 ℤ (n k)) (pr ℤ m n k) 1 j j'
  rw [zpow_one] at e
  exact (congrArg (Semi.res h) e).trans (res_res' _ _ h' _)

def twIdx (b : Fin m) (t : ℤ) (c : ∀ k, Bk n k) : (twB m n b t).ι :=
  Prod.mk (fun _ => c b.succ) (fun _ => c 0)

theorem mchart_le_U (b : Fin m) (t : ℤ) (c : ∀ k, Bk n k) : mchart c ≤ (twB m n b t).U (twIdx b t c) :=
  fun _ hx => ⟨Set.mem_iInter.2 fun _ => mchart_le c _ hx, Set.mem_iInter.2 fun _ => mchart_le c _ hx⟩

theorem blk_le {c c' : ∀ k, Bk n k} {W : (MP ℤ m n).Opens} (hW : W ≤ mchart c ⊓ mchart c') (k : Fin (m + 1)) :
    W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)) :=
  fun _ hx => ⟨mchart_le c k (hW hx).1, mchart_le c' k (hW hx).2⟩

theorem res_twB_g (b : Fin m) (t : ℤ) (c c' : ∀ k, Bk n k) {W : (MP ℤ m n).Opens} (hW : W ≤ mchart c ⊓ mchart c')
    (h : W ≤ (twB m n b t).U (twIdx b t c) ⊓ (twB m n b t).U (twIdx b t c')) :
    Semi.res h ((twB m n b t).g (twIdx b t c) (twIdx b t c')) =
      blockUnit (c b.succ) (c' b.succ) (blk_le hW b.succ) * blockUnit (c 0) (c' 0) (blk_le hW 0) ^ t := by
  have h₁ : W ≤ ((O1 ℤ (n b.succ)).pull (pr ℤ m n b.succ)).U (fun _ => c b.succ) ⊓
      ((O1 ℤ (n b.succ)).pull (pr ℤ m n b.succ)).U (fun _ => c' b.succ) :=
    le_inf (fun _ hx => h hx |>.1.1) (fun _ hx => h hx |>.2.1)
  have h₂ : W ≤ ((O1 ℤ (n 0)).pull (pr ℤ m n 0)).U (fun _ => c 0) ⊓
      ((O1 ℤ (n 0)).pull (pr ℤ m n 0)).U (fun _ => c' 0) :=
    le_inf (fun _ hx => h hx |>.1.2) (fun _ hx => h hx |>.2.2)
  have e₁ := res_pull_g b.succ (fun _ => c b.succ) (fun _ => c' b.succ) h₁ (blk_le hW b.succ)
  have e₂ := res_pull_g 0 (fun _ => c 0) (fun _ => c' 0) h₂ (blk_le hW 0)
  have e₃ : (Semi.res h₂ (((O1 ℤ (n 0)).pull (pr ℤ m n 0)).g (fun _ => c 0) (fun _ => c' 0)) ^ (-t))⁻¹ =
      blockUnit (c 0) (c' 0) (blk_le hW 0) ^ t := by
    rw [zpow_neg, inv_inv]
    exact congrArg (· ^ t) e₂
  exact (res_div_g _ _ (twIdx b t c) (twIdx b t c') h h₁ h₂).trans (congrArg₂ (· * ·) e₁
    ((congrArg (·⁻¹) (map_zpow (Semi.res h₂) _ (-t))).trans e₃))

theorem blockUnit_self {k : Fin (m + 1)} (i : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) i)) : blockUnit i i h = 1 := by
  rw [blockUnit, ratioUnit_self, map_one, map_one]

theorem prod_zpow_single {G : Type*} [CommGroup G] (f : Fin (m + 1) → G) (p q : Fin (m + 1)) (t : ℤ) :
    ∏ k, f k ^ ((Pi.single p 1 + t • Pi.single q 1 : Fin (m + 1) → ℤ) k) = f p * f q ^ t := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zpow_add, Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_eq_single p (fun k _ hk => by simp [hk]) (by simp)]
    simp
  · rw [Finset.prod_eq_single q (fun k _ hk => by simp [hk]) (by simp)]
    simp

variable {B : LB (MP ℤ m n)} {b : Fin m} {t : ℤ}

def uOf (w : LB.Iso B (twB m n b t)) (i : B.ι) (c : ∀ k, Bk n k) : Γ(MP ℤ m n, B.U i ⊓ mchart c)ˣ :=
  Semi.res (le_inf (inf_le_right.trans (mchart_le_U b t c)) inf_le_left) (w.s (twIdx b t c, i))

theorem res_uOf (w : LB.Iso B (twB m n b t)) (i : B.ι) (c : ∀ k, Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ B.U i ⊓ mchart c) (h' : W ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i) :
    Semi.res h (uOf w i c) = Semi.res h' (w.s (twIdx b t c, i)) :=
  res_res' _ _ h' _

theorem frame_uOf {w : LB.Iso B (twB m n b t)} (hw : w.IsGen) (i j : B.ι) (c : ∀ k, Bk n k) :
    Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        B.U i ⊓ B.U j ⊓ mchart c ≤ B.U j ⊓ mchart c) (uOf w j c) =
      Semi.res (inf_le_left : B.U i ⊓ B.U j ⊓ mchart c ≤ B.U i ⊓ B.U j) (B.g i j) *
        Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          B.U i ⊓ B.U j ⊓ mchart c ≤ B.U i ⊓ mchart c) (uOf w i c) := by
  have hc : B.U i ⊓ B.U j ⊓ mchart c ≤ mchart c ⊓ mchart c := le_inf inf_le_right inf_le_right
  have hU := (inf_le_right : B.U i ⊓ B.U j ⊓ mchart c ≤ mchart c).trans (mchart_le_U b t c)
  have hi : B.U i ⊓ B.U j ⊓ mchart c ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i :=
    le_inf hU (inf_le_left.trans inf_le_left)
  have hj : B.U i ⊓ B.U j ⊓ mchart c ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U j :=
    le_inf hU (inf_le_left.trans inf_le_right)
  have e := iso_law hw (twIdx b t c, i) (twIdx b t c, j) hi hj (le_inf hU hU) inf_le_left
  rw [res_twB_g b t c c hc, blockUnit_self, blockUnit_self, one_zpow, one_mul, one_mul] at e
  rw [res_uOf w j c _ hj, res_uOf w i c _ hi]
  exact (eq_inv_mul_iff_mul_eq.1 e).symm

theorem mono_uOf (hB : B.IsLB) {w : LB.Iso B (twB m n b t)} (hw : w.IsGen) (i : B.ι) (c c' : ∀ k, Bk n k) :
    Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
        B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ mchart c) (uOf w i c) =
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ mchart c') (uOf w i c') *
      ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
        ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
          B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^
        (Pi.single b.succ 1 + t • Pi.single 0 1 : Fin (m + 1) → ℤ) k := by
  have hc : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c ⊓ mchart c' := inf_le_right
  have hU := (inf_le_right.trans inf_le_left : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c).trans (mchart_le_U b t c)
  have hU' := (inf_le_right.trans inf_le_right : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c').trans (mchart_le_U b t c')
  have hs : Semi.res (le_inf inf_le_left inf_le_left : B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ B.U i) (B.g i i) = 1 :=
    Units.ext (LB.resG_g_self hB i _)
  have hi : B.U i ⊓ (mchart c ⊓ mchart c') ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i := le_inf hU inf_le_left
  have hi' : B.U i ⊓ (mchart c ⊓ mchart c') ≤ (twB m n b t).U (twIdx b t c') ⊓ B.U i := le_inf hU' inf_le_left
  have e := iso_law hw (twIdx b t c, i) (twIdx b t c', i) hi hi' (le_inf hU hU') (le_inf inf_le_left inf_le_left)
  rw [res_twB_g b t c c' hc] at e
  change _ = _ * (Semi.res _ (B.g i i))⁻¹ * _ at e
  rw [hs, inv_one, mul_one] at e
  rw [res_uOf w i c _ hi, res_uOf w i c' _ hi',
    prod_zpow_single (fun k => blockUnit (c k) (c' k) (blk_le hc k)) b.succ 0 t]
  exact e.trans (mul_comm _ _)

theorem exists_units : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (B : LB (MP ℤ m n)) (c : Fin m) (t : ℤ), B.IsLB → LBIso B (twB m n c t) →
  ∃ u : ∀ (i : B.ι) (c' : ∀ k, Bk n k), Γ(MP ℤ m n, B.U i ⊓ mchart c')ˣ,
    (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U i ⊓ B.U j) (B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U i ⊓ mchart c') (u i c')) ∧
    (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ (Pi.single c.succ 1 + t • Pi.single 0 1 : Fin (m + 1) → ℤ) k) := by
  rintro m n B c t hB ⟨w, hw⟩
  exact ⟨uOf w, frame_uOf hw, mono_uOf hB hw⟩

end GlobalTheory.CompanionTheory.MPDict.TwUnits
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductMeasureStatement
section
noncomputable section

open MeasureTheory Measure Set
open scoped Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.CompanionTheory.ThTot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.ProdMeasPf

section Abstract

variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem isAddFundamentalDomain_join (J : X × Y ≃ᵐ Z) (hJ : ∀ a b, J (a + b) = J a + J b)
    (Γ : AddSubgroup X) (Δ : AddSubgroup Y) (Λ : AddSubgroup Z)
    (hΛ : ∀ z, z ∈ Λ ↔ (J.symm z).1 ∈ Γ ∧ (J.symm z).2 ∈ Δ)
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (F : Set X) (G : Set Y)
    (hF : IsAddFundamentalDomain Γ F μ) (hG : IsAddFundamentalDomain Δ G ν) :
    IsAddFundamentalDomain Λ (J '' (F ×ˢ G)) ((μ.prod ν).map J) := by
  have hm : ∀ R : Set (X × Y), (μ.prod ν).map J (J '' R) = μ.prod ν R := fun R => by
    rw [J.map_apply, Set.preimage_image_eq _ J.injective]
  have htr : ∀ (l : Z) (w : X × Y), l + J w = J (J.symm l + w) := fun l w => by
    rw [hJ, J.apply_symm_apply]
  have himg : ∀ l : Λ, (l +ᵥ (J '' (F ×ˢ G)) : Set Z) =
      J '' ((((⟨(J.symm l.1).1, ((hΛ _).1 l.2).1⟩ : Γ) +ᵥ F : Set X)) ×ˢ
        (((⟨(J.symm l.1).2, ((hΛ _).1 l.2).2⟩ : Δ) +ᵥ G : Set Y))) := by
    intro l
    ext z
    constructor
    · rintro ⟨_, ⟨w, ⟨h1, h2⟩, rfl⟩, rfl⟩
      refine ⟨J.symm l.1 + w, ⟨⟨w.1, h1, rfl⟩, ⟨w.2, h2, rfl⟩⟩, ?_⟩
      exact (htr l.1 w).symm
    · rintro ⟨w, ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩, rfl⟩
      refine ⟨J (a, b), ⟨(a, b), ⟨ha, hb⟩, rfl⟩, ?_⟩
      have : J.symm l.1 + (a, b) = w := Prod.ext h1 h2
      change l.1 + J (a, b) = J w
      rw [htr, this]
  refine ⟨?_, ?_, ?_⟩
  · have hq : QuasiMeasurePreserving J.symm ((μ.prod ν).map J) (μ.prod ν) := by
      refine ⟨J.symm.measurable.aemeasurable, ?_⟩
      rw [Measure.map_map J.symm.measurable J.measurable]
      simp only [MeasurableEquiv.symm_comp_self, Measure.map_id]
      exact Measure.AbsolutelyContinuous.rfl
    rw [J.image_eq_preimage_symm]
    exact (hF.nullMeasurableSet.prod hG.nullMeasurableSet).preimage hq
  · rw [J.measurableEmbedding.ae_map_iff]
    have h1 := (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hF.ae_covers
    have h2 := (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hG.ae_covers
    filter_upwards [h1, h2] with w hw1 hw2
    obtain ⟨g, hg⟩ := hw1
    obtain ⟨d, hd⟩ := hw2
    refine ⟨⟨J (g.1, d.1), (hΛ _).2 (by simp)⟩, (g.1 + w.1, d.1 + w.2), ⟨hg, hd⟩, ?_⟩
    change J (g.1 + w.1, d.1 + w.2) = J (g.1, d.1) + J w
    rw [← hJ]
    rfl
  · intro l l' hll
    change (μ.prod ν).map J ((l +ᵥ (J '' (F ×ˢ G)) : Set Z) ∩ (l' +ᵥ (J '' (F ×ˢ G)) : Set Z)) = 0
    rw [himg, himg, ← Set.image_inter J.injective, hm, Set.prod_inter_prod, Measure.prod_prod]
    have hne : (⟨(J.symm l.1).1, ((hΛ _).1 l.2).1⟩ : Γ) ≠ ⟨(J.symm l'.1).1, ((hΛ _).1 l'.2).1⟩ ∨
        (⟨(J.symm l.1).2, ((hΛ _).1 l.2).2⟩ : Δ) ≠ ⟨(J.symm l'.1).2, ((hΛ _).1 l'.2).2⟩ := by
      by_contra hcon
      push_neg at hcon
      apply hll
      apply Subtype.ext
      apply J.symm.injective
      exact Prod.ext (congrArg Subtype.val hcon.1) (congrArg Subtype.val hcon.2)
    rcases hne with h | h
    · have := hF.aedisjoint h
      rw [show μ _ = 0 from this, zero_mul]
    · have := hG.aedisjoint h
      rw [show ν _ = 0 from this, mul_zero]

end Abstract

variable {D : D7} {r s p : ℕ}

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  funext i j; simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  funext i j; simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  funext i j
  induction i using Fin.addCases with
  | left a => simp [rowT, rowJ]
  | right b => simp [rowB, rowJ]

theorem rowJ_add (x x' : Mx D r p) (z z' : Mx D s p) : rowJ (x + x') (z + z') = rowJ x z + rowJ x' z' := by
  funext i j
  induction i using Fin.addCases with
  | left a => simp [rowJ]
  | right b => simp [rowJ]

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem continuous_rowJ : Continuous (fun z : Mx D r p × Mx D s p => rowJ z.1 z.2) := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.addCases with
  | left a =>
    simpa [rowJ] using (continuous_fst.matrix_elem a j)
  | right b =>
    simpa [rowJ] using (continuous_snd.matrix_elem b j)

def rowH : Mx D r p × Mx D s p ≃ₜ Mx D (r + s) p where
  toFun z := rowJ z.1 z.2
  invFun y := (rowT y, rowB y)
  left_inv z := Prod.ext (rowT_rowJ _ _) (rowB_rowJ _ _)
  right_inv := rowJ_rowT_rowB
  continuous_toFun := continuous_rowJ
  continuous_invFun := continuous_rowT.prodMk continuous_rowB

theorem mem_ratMx_iff (y : Mx D (r + s) p) :
    y ∈ ratMx D (r + s) p ↔ rowT y ∈ ratMx D r p ∧ rowB y ∈ ratMx D s p := by
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨⟨fun i j => γ (Fin.castAdd s i) j, rfl⟩, ⟨fun i j => γ (Fin.natAdd r i) j, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    replace ha : rat a = rowT y := ha
    replace hb : rat b = rowB y := hb
    refine ⟨fun i j => Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) i, ?_⟩
    change rat _ = y
    funext i j
    induction i using Fin.addCases with
    | left u =>
      refine Eq.trans ?_ (congrFun (congrFun ha u) j)
      change incA D (Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) (Fin.castAdd s u)) =
        incA D (a u j)
      rw [Fin.addCases_left]
    | right v =>
      refine Eq.trans ?_ (congrFun (congrFun hb v) j)
      change incA D (Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) (Fin.natAdd r v)) =
        incA D (b v j)
      rw [Fin.addCases_right]

theorem prodMeas : ProdMeas := by
  intro D r s p μr 𝓕r μs 𝓕s μ 𝓕 hr hs h
  obtain ⟨a1, a2, a3, a4, -⟩ := lattice_Mx D r p
  obtain ⟨b1, b2, b3, b4, -⟩ := lattice_Mx D s p
  obtain ⟨c1, c2, c3, c4, -⟩ := lattice_Mx D (r + s) p
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  let J : Mx D r p × Mx D s p ≃ᵐ Mx D (r + s) p := (rowH (D := D) (r := r) (s := s) (p := p)).toMeasurableEquiv
  have hJ : ∀ a b, J (a + b) = J a + J b := fun a b => rowJ_add a.1 b.1 a.2 b.2
  have hJf : (J : Mx D r p × Mx D s p → Mx D (r + s) p) = fun z => rowJ z.1 z.2 := rfl
  let e : Mx D r p × Mx D s p ≃+ Mx D (r + s) p :=
    { (rowH (D := D) (r := r) (s := s) (p := p)).toEquiv with map_add' := hJ }
  have hH : ((μr.prod μs).map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map (μr.prod μs) e continuous_rowJ (continuous_rowT.prodMk continuous_rowB)
  have hF : IsAddFundamentalDomain (ratMx D (r + s) p) (J '' (𝓕r ×ˢ 𝓕s)) ((μr.prod μs).map J) :=
    isAddFundamentalDomain_join J hJ (ratMx D r p) (ratMx D s p) (ratMx D (r + s) p)
      (fun z => mem_ratMx_iff z) μr μs 𝓕r 𝓕s hr.2.1 hs.2.1
  have h1 : (μr.prod μs).map J (J '' (𝓕r ×ˢ 𝓕s)) = 1 := by
    rw [J.map_apply, Set.preimage_image_eq _ J.injective, Measure.prod_prod, hr.2.2, hs.2.2, one_mul]
  have hcov : IsCovolOne (ratMx D (r + s) p) ((μr.prod μs).map J) (J '' (𝓕r ×ˢ 𝓕s)) := ⟨hH, hF, h1⟩
  exact covolOne_measure_eq hcov h

end GlobalTheory.CompanionTheory.ThTot.ProdMeasPf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductThetaOfSchwartzTensor
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ThTot
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.ProductTheta

variable {D : D7} {r s p : ℕ}

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp (continuous_apply (Fin.castAdd s i))

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp (continuous_apply (Fin.natAdd r i))

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  funext i j
  simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  funext i j
  simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  funext i j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [rowT, rowB, rowJ]

theorem continuous_rowJ :
    Continuous fun z : Mx D r p × Mx D s p => rowJ z.1 z.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simpa [rowJ, Function.comp_def] using (continuous_apply j).comp ((continuous_apply a).comp continuous_fst)
  · simpa [rowJ, Function.comp_def] using (continuous_apply j).comp ((continuous_apply b).comp continuous_snd)

def rowHomeo : Mx D r p × Mx D s p ≃ₜ Mx D (r + s) p where
  toFun z := rowJ z.1 z.2
  invFun y := (rowT y, rowB y)
  left_inv z := by simp [rowT_rowJ, rowB_rowJ]
  right_inv y := rowJ_rowT_rowB y
  continuous_toFun := continuous_rowJ
  continuous_invFun := continuous_rowT.prodMk continuous_rowB

theorem rowT_mul (y : Mx D (r + s) p) (a : Mx D p p) :
    rowT (HMul.hMul y a : Mx D (r + s) p) = (HMul.hMul (rowT y) a : Mx D r p) := rfl

theorem rowB_mul (y : Mx D (r + s) p) (a : Mx D p p) :
    rowB (HMul.hMul y a : Mx D (r + s) p) = (HMul.hMul (rowB y) a : Mx D s p) := rfl

theorem pr_split {b : HermE D (r + s)} {br : HermE D r} {bs : HermE D s} (h : IsBlockSL2Embedding b br bs)
    (x y : Mx D (r + s) p) :
    pr b x y = pr br (rowT x) (rowT y) + pr bs (rowB x) (rowB y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  funext i j
  simp only [pr, Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, Fin.sum_univ_add, h1, h2, h3, h4,
    map_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  rfl

theorem halfTr_add (u v : AE D) : halfTr (u + v) = halfTr u + halfTr v := by
  simp only [halfTr, trA, map_add (f := _), mul_add]

theorem npow_half_mul (x : ℝ≥0) (hx : x ≠ 0) :
    npow x ((r : ℂ) / 2) * npow x ((s : ℂ) / 2) = npow x (((r + s : ℕ) : ℂ) / 2) := by
  have hx' : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
  simp only [npow]
  rw [← Complex.cpow_add _ _ hx']
  congr 1
  push_cast
  ring

theorem absA_ne_zero (u : (AE D)ˣ) : absA D u ≠ 0 := by
  intro h
  have := map_mul (absA D) u u⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at this
  exact one_ne_zero this

theorem prodTh_of_schwTensor : SchwTensor → ProdTh := by
  intro hT D r s p μr 𝓕r μs 𝓕s hμr hμs ψ hψ χr χs θ hθ br bs b hb Ωr Ωs hr hs
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI : SecondCountableTopology (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.2.1
  haveI : SecondCountableTopology (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.2.1
  refine ⟨fun h => hT D θ hθ r s p _ (hr.mem h) _ (hs.mem h), ?_, ?_, ?_, ?_, ?_⟩
  · have c1 : Continuous fun u : G D p × Mx D (r + s) p => ((u.1, rowT u.2) : G D p × Mx D r p) :=
      continuous_fst.prodMk (continuous_rowT.comp continuous_snd)
    have c2 : Continuous fun u : G D p × Mx D (r + s) p => ((u.1, rowB u.2) : G D p × Mx D s p) :=
      continuous_fst.prodMk (continuous_rowB.comp continuous_snd)
    exact (hr.cont.comp c1).mul (hs.cont.comp c2)
  · intro C hC
    obtain ⟨Mr, hMr, h1⟩ := hr.maj C hC
    obtain ⟨Ms, hMs, h2⟩ := hs.maj C hC
    refine ⟨_, hT D θ hθ r s p _ hMr _ hMs, fun h hh y => ?_⟩
    rw [norm_mul, norm_mul]
    exact mul_le_mul (h1 h hh _) (h2 h hh _) (norm_nonneg _) (norm_nonneg _)
  · intro g a hg h y
    have e := npow_half_mul (r := r) (s := s) (absA D (Matrix.GeneralLinearGroup.det a)) (absA_ne_zero _)
    rw [hr.levi g a hg h, hs.levi g a hg h, rowT_mul, rowB_mul, ← e]
    simp only [MonoidHom.mul_apply, Circle.coe_mul]
    ring
  · intro g c hg h y
    rw [hr.unip g c hg h, hs.unip g c hg h, pr_split hb, mul_add, Matrix.trace_add, halfTr_add,
      AddChar.map_add_eq_mul]
    ring
  · intro g hg h x
    haveI := hμr.1
    haveI := hμs.1
    haveI : LocallyCompactSpace (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.1
    haveI : LocallyCompactSpace (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.1
    have hemb : MeasurableEmbedding (fun z : Mx D r p × Mx D s p => rowJ z.1 z.2) :=
      (rowHomeo (D := D) (r := r) (s := s) (p := p)).measurableEmbedding
    rw [hemb.integral_map, hr.weyl g hg h, hs.weyl g hg h, ← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [rowT_rowJ, rowB_rowJ, pr_split hb, Matrix.trace_add, map_add (f := _), AddChar.map_add_eq_mul]
    ring

end GlobalTheory.CompanionTheory.ThTot.ProductTheta

end
end

