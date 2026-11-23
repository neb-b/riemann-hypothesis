module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.JacNeZeroIffSpanEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BoxProductsSpanExternalPowersOfBoxSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.PowSpan

variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}

def ev (p : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp
    ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_cst (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (cst p U c) = ev (r ≫ p) z c :=
  (gs_res r z le_top h _).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq _ z ⊤ trivial _))

theorem sum_mul_cons {T : Type} [CommRing T] {E₂ E : R →+* T} (h₂ : E₂ = E) {n N : ℕ}
    (G : Fin (n + 1) → Fin N → T) (q : Fin N → (Fin n → Fin N) → R) :
    ∑ k, (∑ I, E₂ (q k I) * ∏ d : Fin n, G d.succ (I d)) * G 0 k =
      ∑ I : Fin (n + 1) → Fin N, E (q (I 0) (Fin.tail I)) * ∏ d, G d (I d) := by
  subst h₂
  rw [← (Fin.consEquiv fun _ => Fin N).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Fin.tail_cons]
  ring

theorem span_ev (A : Over (Sp R)) (L : LB A.left) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)) (hL : L.IsLB)
    (hb : ∀ T : Over (Sp R), GlobalTheory.RelBasis.BoxSpan b (snd A T).left (fst A T).left) (n : ℕ) :
    ∀ (s : LB.Sec (LB.LinComb L (K := Fin n) (fun c => (Out.powPr A c).left) (fun _ => t))),
      ∃ q : (Fin n → Fin N) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj A n).left) (z : Z) J, Good L z J →
        sval s r z J = ∑ I, ev (r ≫ (Out.powObj A n).hom) z (q I) *
          ∏ c, gs (r ≫ (Out.powPr A c).left) z (L.U (J (r ≫ (Out.powPr A c).left)))
            ((b (I c)).f (J (r ≫ (Out.powPr A c).left))) := by
  induction n with
  | zero =>
    intro s
    have hW : LB.wchart L (K := Fin 0) (fun c => (Out.powPr A c).left) Fin.elim0 = ⊤ :=
      top_le_iff.1 fun _ _ => Set.mem_iInter.2 fun k => k.elim0
    haveI : IsIso (Out.powObj A 0).hom := inferInstanceAs (IsIso (𝟙 (Sp R)))
    obtain ⟨c, hc⟩ := (cst_bijective (Out.powObj A 0).hom hW).2 (s.f Fin.elim0)
    refine ⟨fun _ => c, fun Z r z J hJ => ?_⟩
    rw [sval_of s r z J Fin.elim0 (fun k => k.elim0), ← hc, Fintype.sum_unique, Fin.prod_univ_zero, _root_.mul_one]
    exact gs_cst _ r z _ (Set.mem_iInter.2 fun k => k.elim0) c
  | succ n ih =>
    intro s
    have hF : FormEq (K := Fin (n + 1)) (K' := Fin n ⊕ PUnit) (fun c => (Out.powPr A c).left) (fun _ => t)
        (Sum.elim (fun k => (snd A (Out.powObj A n)).left ≫ (Out.powPr A k).left)
          (fun _ => (fst A (Out.powObj A n)).left))
        (Sum.elim (fun _ => t) (fun _ => t)) := fun U _ h => by
      rw [Fin.prod_univ_succ, Fintype.prod_sum_type, mul_comm]
      exact congrArg₂ (· * ·) rfl (Fintype.prod_unique
        (fun _ : PUnit => h (fst A (Out.powObj A n)).left ^ t)).symm
    obtain ⟨v, hv⟩ := exists_sec hL hF s
    obtain ⟨a, ha⟩ := hb (Out.powObj A n) (Fin n) (fun c => (Out.powPr A c).left) (fun _ => t) v
    choose q hq using fun i => ih (a i)
    refine ⟨fun I => q (I 0) (Fin.tail I), fun Z r z J hJ => ?_⟩
    refine (hv Z r z J hJ).symm.trans ((ha Z r z J hJ).trans ?_)
    have e₂ : (r ≫ (snd A (Out.powObj A n)).left) ≫ (Out.powObj A n).hom =
        r ≫ (Out.powObj A (n + 1)).hom :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w (snd A (Out.powObj A n))))
    refine (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (hq i Z _ z J hJ) rfl).trans ?_
    exact sum_mul_cons (congrArg (ev · z) e₂)
      (fun d j => gs (r ≫ (Out.powPr A d).left) z (L.U (J (r ≫ (Out.powPr A d).left)))
          ((b j).f (J (r ≫ (Out.powPr A d).left)))) q

theorem boxProducts_span_of_boxSpan : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (L : LB A.left) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)), L.IsLB → (∀ T : Over (Sp R), GlobalTheory.RelBasis.BoxSpan b (snd A T).left (fst A T).left) → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb L (K := Fin n) (fun c => (Out.powPr A c).left) (fun _ => t))), ∃ q : (Fin n → Fin N) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj A n).left) (z : Z) J, Good L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr A c).left) z (L.U (J (r ≫ (Out.powPr A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr A c).left))) := by
  intro R _ A L t N b hL hb n s
  obtain ⟨q, hq⟩ := span_ev A L t N b hL hb n s
  refine ⟨q, fun Z r z J hJ => (hq Z r z J hJ).trans (Finset.sum_congr rfl fun I _ => ?_)⟩
  rw [gs_cst _ r z ⊤ trivial]

end GlobalTheory.PowSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EqOfSimilitudeIsoQuotientKernelInvariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.KeyKa

section
variable {R : Type} [CommRing R] (x : KeyIn R) (al : Matrix (Fin 4) (Fin 4) ℤ) (r₀ : Fin 4)

def rowEmb : x.P.A ⟶ Out.powObj x.P.A 4 :=
  (Out.powIsLimit x.P.A 4).lift (Fan.mk x.P.A fun c => (𝟙 x.P.A) ^ al r₀ c)

theorem rowEmb_pr (c : Fin 4) : rowEmb x al r₀ ≫ Out.powPr x.P.A c = (𝟙 x.P.A) ^ al r₀ c :=
  (Out.powIsLimit x.P.A 4).fac (Fan.mk x.P.A fun c => (𝟙 x.P.A) ^ al r₀ c) ⟨c⟩

theorem rowEmb_alMap {m : ℕ} (hal : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (r : Fin 4)
    (ζ : Pt x) : rowEmb x al r₀ ≫ alMap x al r ζ =
      (if r = r₀ then (𝟙 x.P.A) ^ m else 1) * (toUnit x.P.A ≫ ζ) := by
  have := x.P.isAb.comm
  have h : al r₀ 0 * al r 0 + (al r₀ 1 * al r 1 + (al r₀ 2 * al r 2 + al r₀ 3 * al r 3)) =
      if r = r₀ then (m : ℤ) else 0 := by
    have := congrFun (congrFun hal r₀) r
    simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, mul_ite, _root_.mul_one, mul_zero, eq_comm (a := r₀)] at this
    rw [← this]; ring
  rw [alMap, MonObj.comp_mul, ← Category.assoc, comp_toUnit]
  congr 1
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul, GrpObj.comp_zpow,
    rowEmb_pr, _root_.mul_one, ← zpow_mul, ← zpow_add]
  refine (congrArg (fun n : ℤ => (𝟙 x.P.A) ^ n) h).trans ?_
  split_ifs
  · exact zpow_natCast _ _
  · exact zpow_zero _

theorem transl_rowEmb (δ : Pt x) : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A) ≫ rowEmb x al r₀ =
    rowEmb x al r₀ ≫ ((toUnit (Out.powObj x.P.A 4) ≫ δ ≫ rowEmb x al r₀) * 𝟙 (Out.powObj x.P.A 4)) := by
  have := x.P.isAb.comm
  refine (Out.powIsLimit x.P.A 4).hom_ext fun ⟨c⟩ => ?_
  change (_ ≫ _) ≫ Out.powPr x.P.A c = (_ ≫ _) ≫ Out.powPr x.P.A c
  rw [Category.assoc, Category.assoc, rowEmb_pr, MonObj.mul_comp _ _ (Out.powPr x.P.A c), MonObj.comp_mul, Category.id_comp, Category.assoc,
    Category.assoc, rowEmb_pr, ← Category.assoc (rowEmb x al r₀), comp_toUnit]
  simp only [GrpObj.comp_zpow, Category.comp_id, mul_zpow]

end

theorem eq_of_similitude_invariant : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ ξ' : Fin 4 → Pt x) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (w' : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ' r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → w.IsGen → w'.IsGen → (∀ v : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4, (∀ r, v ≫ alMap x al r 1 = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → val w (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w' r z J = val w' (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w r z J) → ξ = ξ' := by
  intro laws K _ _ x m al ξ ξ' w w' hm hal hw hw' hinv
  have hL := x.P.isLB
  have hm0 : (m : ℤ) ≠ 0 := fun h => hm (by rw [Int.natCast_eq_zero.1 h, Nat.cast_zero])
  have hal' : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have hd : al.det ≠ 0 := fun h => by
      have := congrArg Matrix.det hal
      rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at this
      exact pow_ne_zero _ hm0 this.symm
    have h1 : (al * al.transpose - (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) * al = 0 := by
      rw [sub_mul, _root_.mul_assoc, hal, Matrix.mul_smul, Matrix.smul_mul, _root_.mul_one,
        _root_.one_mul, sub_self]
    have h2 := congrArg (· * al.adjugate) h1
    simp only [_root_.mul_assoc, Matrix.mul_adjugate, zero_mul, Matrix.mul_smul, _root_.mul_one] at h2
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hd)
  funext r₀
  obtain ⟨g, hg⟩ := DVR.exists_gen_of_local (V := K) x.P.L hL (K := Fin 4 ⊕ Fin 4)
    (Sum.elim (fun r => (ξ r).left) (fun r => (ξ' r).left))
    (Sum.elim (fun r => if r = r₀ then 0 else -1) (fun r => if r = r₀ then 0 else 1))
  let i := rowEmb x al r₀
  have hu₀ := DVR.mulGen_isGen x.P.L _ _ _ _ _ _
    (DVR.mulGen_isGen x.P.L _ _ _ _ _ _ (DVR.pullGen_isGen x.P.L _ _ w hw i.left)
      (DVR.invGen_isGen x.P.L _ _ _ (DVR.pullGen_isGen x.P.L _ _ w' hw' i.left)))
    (DVR.pullGen_isGen x.P.L _ _ g hg (toUnit x.P.A).left)
  obtain ⟨u, hu, hval⟩ := exists_gen hL (K' := Fin 2)
    (φ' := ![((𝟙 x.P.A) ^ m * (toUnit x.P.A ≫ ξ r₀)).left, ((𝟙 x.P.A) ^ m * (toUnit x.P.A ≫ ξ' r₀)).left])
    (ε' := ![1, -1]) (by
      intro U _ h
      have e : ∀ (r : Fin 4) (ζ : Pt x), i.left ≫ (alMap x al r ζ).left =
          ((if r = r₀ then (𝟙 x.P.A) ^ m else 1) * (toUnit x.P.A ≫ ζ)).left := fun r ζ =>
        congrArg (fun q => q.left) (rowEmb_alMap x al r₀ hal' r ζ)
      have e' : ∀ ζ : Pt x, (toUnit x.P.A).left ≫ ζ.left = (toUnit x.P.A ≫ ζ).left := fun _ => rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, e, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, neg_neg]
      simp only [← Finset.prod_mul_distrib]
      rw [Finset.prod_eq_single r₀ (fun r _ hr => ?_) (fun hr => absurd (Finset.mem_univ _) hr)]
      · simp only [if_true, zpow_zero, _root_.mul_one, zpow_neg]
        rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.mul_one]
      · simp only [if_neg hr, _root_.one_mul, zpow_one, zpow_neg, e']
        rw [_root_.mul_mul_mul_comm, mul_inv_cancel_comm, inv_mul_cancel_comm, inv_mul_cancel]) _ hu₀
  refine GlobalTheory.eq_of_invariantGen_translates laws K x.P m (ξ r₀) (ξ' r₀) u hm hu fun δ hδ y J hJ => ?_
  have hv := hinv (δ ≫ i) (fun r => by
    rw [Category.assoc, rowEmb_alMap x al r₀ hal', MonObj.comp_one, _root_.mul_one]
    split_ifs
    · rw [MonObj.comp_pow, Category.comp_id, hδ]
    · exact MonObj.comp_one _) _ i.left y J hJ
  have e₁ : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A).left ≫ i.left =
      i.left ≫ ((toUnit (Out.powObj x.P.A 4) ≫ δ ≫ i) * 𝟙 (Out.powObj x.P.A 4)).left :=
    congrArg (fun q => q.left) (transl_rowEmb x al r₀ δ)
  have e₂ : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A).left ≫ (toUnit x.P.A).left = (toUnit x.P.A).left :=
    congrArg (fun q => q.left) (comp_toUnit ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A))
  rw [hval _ _ y J hJ, hval _ _ y J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
    val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, e₁, Category.id_comp,
    Category.id_comp]
  erw [e₂]
  congr 1
  rw [mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq, hv, mul_comm]

end GlobalTheory.KeyKa

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsLevBasisReal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa.LevelBasis

section Real
open ReciprocityTheory.PTheta Matrix

theorem isLevel_iff {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (l : ℕ) (F : (Fin g → ℂ) → ℂ) :
    IsLevel τ (ofRealVec a) (ofRealVec b) l F ↔ F ∈ thetaLevelChar a b l τ := by
  have key : ∀ (m n : Fin g → ℤ) (z : Fin g → ℂ),
      Complex.exp (2 * Real.pi * Complex.I * (ofRealVec a ⬝ᵥ (fun i => (m i : ℂ)) - ofRealVec b ⬝ᵥ (fun i => (n i : ℂ)) -
        ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z)) ^ l =
      eC ((l : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec m - ofRealVec b ⬝ᵥ ofIntVec n)) *
        eC (-(l : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) := by
    intro m n z
    unfold eC
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    unfold ofIntVec
    ring
  have e : ∀ (m n : Fin g → ℤ) (z : Fin g → ℂ),
      z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) = z + τ *ᵥ ofIntVec n + ofIntVec m := by
    intro m n z
    unfold ofIntVec
    abel
  rw [mem_thetaLevelChar]
  refine and_congr Iff.rfl ⟨fun h n m z => ?_, fun h m n z => ?_⟩
  · rw [← key, ← e]; exact h m n z
  · rw [key, e]; exact h n m z

theorem holFam_levelTheta {g : ℕ} (a b : Fin g → ℝ) {l : ℕ} (hl : 0 < l) (c : Fin g → ℤ) :
    HolFam (Key.phDom g) (fun p => levelTheta a b l (per p) c) := by
  have H := thetaHolo_of_domainOpen_of_mTest siegelSubDomain_and_domainOpen.2 thetaMTest_holds (Fin g)
    ((fun i => (c i : ℝ) / l) + a) ((l : ℝ) • b)
  have hd : Differentiable ℂ (fun q : (Fin g → Fin g → ℂ) × (Fin g → ℂ) =>
      (((l : ℂ) • q.2, fun i j => (l : ℂ) * ((1 / 2 : ℂ) * (q.1 i j + q.1 j i))) :
        (Fin g → ℂ) × (Fin g → Fin g → ℂ))) := by
    fun_prop
  refine (H.comp hd.differentiableOn fun q hq => ?_).congr fun q _ => rfl
  exact siegelSubDomain_and_domainOpen.1 _ (smul_mem_siegelH hq.1 hl)

theorem exists_levBasis_real (g : ℕ) (a b : Fin g → ℝ) {l : ℕ} (hl : 0 < l) :
    ∃ Th : Fin (l ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ, LevBasis (ofRealVec a) (ofRealVec b) l Th := by
  let e : Fin (l ^ g) ≃ (Fin g → Fin l) := finFunctionFinEquiv.symm
  let r : Fin (l ^ g) → Fin g → ℤ := fun k i => ((e k i : ℕ) : ℤ)
  have hr : Function.Bijective fun k i => (r k i : ZMod l) := (@GlobalTheory.bijective_fin_zmod (Fin g) l hl).comp e.bijective
  refine ⟨fun k p => levelTheta a b l (per p) (r k), fun k => holFam_levelTheta a b hl _, fun p hp =>
    ⟨fun k => (isLevel_iff _ _ _ _ _).2 (levelTheta_mem hp hl _), fun F hF => ?_⟩⟩
  let B := thetaLevelCharBasis a b (τ := per p) hp hl hr
  have hF' := (isLevel_iff _ _ _ _ _).1 hF
  have hB : ∀ (c : Fin (l ^ g) → ℂ) z, ((∑ k, c k • B k : thetaLevelChar a b l (per p)) : (Fin g → ℂ) → ℂ) z =
      ∑ k, c k * levelTheta a b l (per p) (r k) z := fun c z => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (congrFun (thetaLevelCharBasis_apply (τ := per p) hp hl hr k) z)
  refine ⟨fun k => B.repr ⟨F, hF'⟩ k, fun z => ?_, fun c hc => ?_⟩
  · rw [← hB, B.sum_repr]
  · have : (⟨F, hF'⟩ : thetaLevelChar a b l (per p)) = ∑ k, c k • B k := Subtype.ext (funext fun z => by
      rw [hB]; exact hc z)
    funext k
    rw [this, B.repr_sum_self]

end Real

theorem exists_levBasis : ∀ (g : ℕ) (a b : Fin g → ℂ) (l : ℕ), charHalf g a b → 1 ≤ l → ∃ Th : Fin (l ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ, LevBasis a b l Th := by
  intro g a b l h hl
  have := exists_levBasis_real g (fun i => (a i).re) (fun i => (b i).re) (l := l) hl
  rwa [TorusAlg.ofRealVec_re h.1, TorusAlg.ofRealVec_re h.2] at this

end GlobalTheory.KeyKa.LevelBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisingUnitSimilitudeOriginStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.exists_normalising_unit_similitude_origin : ∀ (R : Type) [CommRing R] (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ : Fin 4 → Pt x) (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2])) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), m ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → (∀ c, (List.ofFn fun r : Fin 4 => ξ r ^ al r c).prod = 1) → mu.IsGen → w.IsGen → ∃ rho : Rˣ, ∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J → (val w (eSec (Out.powObj x.P.A 4)) p J ^ (m ^ 2) * ∏ r, val mu (ξ r).left p J).val = gs (𝟙_ (Over (Sp R))).hom p ⊤ (cst (𝟙 (Sp R)) ⊤ rho) * (val x.rig (𝟙 _) p J ^ (4 - 4 * (m : ℤ) ^ 3)).val := by
  first | exact @GlobalTheory.SimilUnit.exists_normalising_unit | exact GlobalTheory.SimilUnit.exists_normalising_unit | (intros; apply GlobalTheory.SimilUnit.exists_normalising_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FiniteOfIsClosedSingleton
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.TransvFin

theorem valT_eq_zero_of_notMem {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ w ⁻¹ᵁ U) (f : Γ(X, U)) (p : Sp K) (hp : w p ∉ X.basicOpen f) : valT (T := K) w U f = 0 := by
  by_contra hne
  have h1 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((w.appLE U ⊤ h).hom f)) := by
    have e : valT (T := K) w U f = _ := dif_pos h
    exact e ▸ Ne.isUnit hne
  have h2 : IsUnit ((w.appLE U ⊤ h).hom f) := by
    have := h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rwa [Iso.hom_inv_id_apply] at this
  have h3 := (Sp K).basicOpen_of_isUnit h2
  rw [Scheme.basicOpen_appLE] at h3
  exact hp ((h3.ge (x := p) trivial).2)

theorem eq_of_specializes {X : Scheme.{0}} {J : Type} {U : X.Opens} (f : J → Γ(X, U)) {y y' : X} (h : y' ⤳ y)
    (hy : y ∈ U)
    (hf : Ideal.span (Set.range fun i => gs (𝟙 X) y U (f i)) = IsLocalRing.maximalIdeal (X.presheaf.stalk y))
    (h0 : ∀ i, y' ∉ X.basicOpen (f i)) : y' = y := by
  by_contra hne
  have hn : ¬ y ⤳ y' := fun h' => hne (h.antisymm h').eq
  rw [specializes_iff_forall_open] at hn
  push_neg at hn
  obtain ⟨V, hV, hV1, hV2⟩ := hn
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y) (U := ⊤) trivial
  have hyW' : y' ∈ W := h.mem_open W.isOpen hyW
  obtain ⟨g, hg, hg'⟩ := hW.exists_basicOpen_le (V := ⟨V, hV⟩) ⟨y', hV1⟩ hyW'
  have hle : IsLocalRing.maximalIdeal (X.presheaf.stalk y) ≤
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y')).comap (X.presheaf.stalkSpecializes h).hom := by
    rw [← hf, Ideal.span_le]
    rintro _ ⟨i, rfl⟩ hu
    refine h0 i ((X.mem_basicOpen (f i) y' (h.mem_open U.isOpen hy)).2 ?_)
    have e : gs (𝟙 X) y U (f i) = (X.presheaf.germ U y hy).hom (f i) := gs_eq (𝟙 X) y U hy (f i)
    beta_reduce at hu
    rwa [e, TopCat.Presheaf.germ_stalkSpecializes_apply] at hu
  have hm : (X.presheaf.germ W y hyW).hom g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
    fun hu => hV2 (hg ((X.mem_basicOpen g y hyW).2 hu))
  refine hle hm ?_
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact (X.mem_basicOpen g y' hyW').1 hg'

theorem finite_of_isClosed_singleton {T : Type} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T]
    [QuasiSober T] {Z : Set T} (hZ : IsClosed Z) (h : ∀ y ∈ Z, IsClosed ({y} : Set T)) : Z.Finite := by
  obtain ⟨S, hS, hc, hi, rfl⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hS.sUnion fun t ht => ?_
  obtain ⟨y, hy⟩ := QuasiSober.sober (hi t ht) (hc t ht)
  rw [← hy.def, (h y ⟨t, ht, hy.mem⟩).closure_eq]
  exact Set.finite_singleton y

end GlobalTheory.TransvFin


open GlobalTheory.TransvFin in
theorem GlobalTheory.KeyKa.exists_etZ_of_jac_ne_zero : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n), (∀ (z : Pt x) (c : x.P.L.ι), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → (∀ i, valT (T := K) z.left (x.P.L.U c) ((s i).f c) = 0) → jac x s z c ≠ 0) → ∃ (d : ℕ) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), EtZ x s z ch := by
  intro K _ _ x n s hs
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  have : IsProper x.P.A.hom := x.P.isAb.proper
  have : JacobsonSpace x.P.A.left := LocallyOfFiniteType.jacobsonSpace x.P.A.hom
  have : IsLocallyNoetherian x.P.A.left := LocallyOfFiniteType.isLocallyNoetherian x.P.A.hom
  have : CompactSpace x.P.A.left := QuasiCompact.compactSpace_of_compactSpace x.P.A.hom
  have : IsNoetherian x.P.A.left := {}
  let Z : Set x.P.A.left := {y | ∀ i, y ∉ Out.nonzeroLocus (s i)}
  have hZ : IsClosed Z := by
    have e : Z = ⋂ i, (Out.nonzeroLocus (s i) : Set x.P.A.left)ᶜ := by
      ext y
      simp [Z]
    rw [e]
    exact isClosed_iInter fun i => (Out.nonzeroLocus (s i)).isOpen.isClosed_compl
  have hb : ∀ y ∈ Z, ∀ c i, y ∉ x.P.A.left.basicOpen ((s i).f c) := fun y hy c i h =>
    hy i (TopologicalSpace.Opens.mem_iSup.2 ⟨c, h⟩)
  have key : ∀ y ∈ Z, IsClosed ({y} : Set x.P.A.left) → ∃ (z : Pt x) (c : x.P.L.ι), (∀ p, z.left p = y) ∧
      ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c ∧ ∀ i, valT (T := K) z.left (x.P.L.U c) ((s i).f c) = 0 := by
    intro y hy hc
    let z : Pt x := Over.homMk (pointOfClosedPoint (K := K) x.P.A.hom y hc)
      (pointOfClosedPoint_comp (K := K) x.P.A.hom y hc)
    have hz (p) : z.left p = y := pointOfClosedPoint_apply (K := K) x.P.A.hom y hc p
    obtain ⟨c, hyc⟩ := TopologicalSpace.Opens.mem_iSup.1 (x.P.isLB.cover.ge (x := y) trivial)
    have ht : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c := fun p _ => (congrArg (· ∈ x.P.L.U c) (hz p)).mpr hyc
    exact ⟨z, c, hz, ht, fun i => valT_eq_zero_of_notMem z.left ht _ (IsLocalRing.closedPoint K)
      fun h => hb y hy c i ((congrArg (· ∈ x.P.A.left.basicOpen ((s i).f c)) (hz _)).mp h)⟩
  have hcl : ∀ y ∈ Z, IsClosed ({y} : Set x.P.A.left) := by
    intro y' hy'
    obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints (Z := closure ({y'} : Set x.P.A.left))
      ⟨y', subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    have hsp : y' ⤳ y := specializes_iff_mem_closure.2 hy
    obtain ⟨z, c, hz, ht, h0⟩ := key y (hsp.mem_closed hZ hy') hc
    have h1 := (jac_ne_zero_iff_span_eq_maximalIdeal K x n s z c (IsLocalRing.closedPoint K) ht h0).1 (hs z c ht h0)
    have hU : z.left (IsLocalRing.closedPoint K) ∈ x.P.L.U c := ht (x := IsLocalRing.closedPoint K) trivial
    have e := eq_of_specializes (fun i => (s i).f c) ((hz _).symm ▸ hsp) hU h1 (hb y' hy' c)
    rw [e.trans (hz _)]
    exact hc
  have hfin := finite_of_isClosed_singleton hZ hcl
  obtain ⟨d, ⟨e⟩⟩ := Finite.exists_equiv_fin Z (h := hfin)
  choose z c hz ht h0 using fun y : Z => key y y.2 (hcl y y.2)
  refine ⟨d, fun a => z (e.symm a), fun a => c (e.symm a), fun a => ht _, fun a => h0 _,
    fun a => (hs _ _ (ht _) (h0 _)).isUnit, fun a a' hne p h => hne ?_,
    fun y hy => ⟨e ⟨y, hy⟩, IsLocalRing.closedPoint K, ?_⟩⟩
  · exact e.symm.injective (Subtype.ext ((hz _ p).symm.trans (h.trans (hz _ p))))
  · exact (hz _ _).trans (congrArg Subtype.val (e.symm_apply_apply ⟨y, hy⟩))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KTrivBoxLBPowObj
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem kTriv_boxLB_powObj : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (j : ℕ),
    Out.KTriv (Out.powObj P.A j) (Out.boxLB P.L (Out.powPr P.A (n := j))) := by
  intro R _ P j
  have : IsCommMonObj P.A := P.isAb.comm
  exact _root_.GlobalTheory.kTriv_boxLB _ (Out.powObj P.A j) P.A j (Out.powIsPowGrp P.A j) P.L P.isLB P.ktriv

end GlobalTheory
end

