module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPreUOfFibres
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedExpansionCoefficients
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TrCoef

theorem exists_nestSec {X X' Y : Scheme.{0}} {L : LB X} {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (ε : J → ℤ) (ψ : K → (Y ⟶ X')) (δ : K → ℤ)
    (s : LB.Sec (LB.LinComb L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2))) :
    ∃ T : LB.Sec (LB.LinComb (LB.LinComb L F ε) ψ δ), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (I : (Z ⟶ X) → L.ι), Good L z I → sval T r z (fun χ j => I (χ ≫ F j)) = sval s r z I := by
  have le : ∀ q : K → J → L.ι, LB.wchart (LB.LinComb L F ε) ψ q ≤
      LB.wchart L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => q p.1 p.2) := fun q y hy =>
    Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
  have v : ∀ (q : K → J → L.ι) (y : Y) (hy : y ∈ LB.wchart (LB.LinComb L F ε) ψ q),
      gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (le q)).op).hom (s.f fun p => q p.1 p.2)) =
        gs (𝟙 Y) y _ (s.f fun p => q p.1 p.2) := fun q y hy => gs_res _ y (le q) hy _
  refine ⟨⟨fun q => (Y.presheaf.map (homOfLE (le q)).op).hom (s.f fun p => q p.1 p.2),
    fun q q' => fn_ext fun y hy => ?_⟩, fun Z r z I hI => ?_⟩
  · have htr : trF (L := LB.LinComb L F ε) ψ δ (𝟙 Y) y q q' =
        trF (L := L) (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2) (𝟙 Y) y
          (fun p => q p.1 p.2) (fun p => q' p.1 p.2) := by
      refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ δ k)
        (gm_linComb L F ε (𝟙 Y ≫ ψ k) y (q k) (q' k) (Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.1 hy.2 k))).trans ?_
      simp only [trF, Fintype.prod_prod_type, ← Finset.prod_zpow, ← zpow_mul, Category.assoc, mul_comm]
    refine ((gs_res (𝟙 Y) y _ hy _).trans (v q y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
        (congrArg Units.val (gm_linComb (LB.LinComb L F ε) ψ δ (𝟙 Y) y q q' hy.1 hy.2)))
        ((gs_res (𝟙 Y) y _ hy _).trans (v q' y hy.2)))).symm)
    refine (sec_trans s (𝟙 Y) y (le q hy.1) (le q' hy.2)).trans ?_
    rw [← htr]
    rfl
  · have hI' : Good (LB.LinComb L F ε) z (fun χ j => I (χ ≫ F j)) := fun χ => hI.mem F χ
    have hm := hI'.mem ψ r
    rw [sval_of s r z I (fun p => I ((r ≫ ψ p.1) ≫ F p.2)) (fun p => by rw [Category.assoc])]
    exact gs_res r z (le _) hm _

end GlobalTheory.MumCmp.TrCoef

namespace GlobalTheory.MumCmp.TrCoef

theorem formEq_coef {R : Type} [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (g : GtPt D (𝟙_ (Over (Sp R)))) (χ₂ : D₂.X) (χ : D.X) (hc : D₂.c χ₂ ≫ β = D.c χ) :
    FormEq (Sum.elim (fun k => GlobalTheory.MumCmp.twφ D₂ D β g.b 0 ≫ D.famφB χ k)
        (Sum.elim (fun k => (toUnit D₂.P.A).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b χ k)
          (fun k => (toUnit D₂.P.A).left ≫ (![g.b.left, η[D.P.A].left] : Fin 2 → _) k)))
      (Sum.elim (DegPre.famε 1) (Sum.elim DegPre.gtε ![-1, 1]))
      (fun p : Fin 4 × Fin 3 => D₂.famφB χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b p.2)
      (fun p => DegPre.famε 1 p.1 * GlobalTheory.MumCmp.twε p.2) := by
  intro U _ h
  have hu : ∀ x : D₂.P.A ⟶ D₂.P.A, x ≫ toUnit D₂.P.A = toUnit D₂.P.A := fun x => toUnit_unique _ _
  have ht : ∀ x : D₂.P.A ⟶ D₂.P.A, ∏ i, h (x.left ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i) ^ GlobalTheory.MumCmp.twε i =
      h ((x ≫ β) * (toUnit D₂.P.A ≫ g.b)).left * (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left := by
    intro x
    rw [Fin.prod_univ_three]
    show h (x ≫ (β * (toUnit D₂.P.A ≫ g.b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₂.P.A ≫ g.b).left ^ (-1 : ℤ) *
      h (x ≫ toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
    rfl
  have hx : ∀ k, D₂.famφB χ₂ k = ((![𝟙 D₂.P.A, 𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂), toUnit D₂.P.A ≫ D₂.c χ₂, 1] :
      Fin 4 → (D₂.P.A ⟶ D₂.P.A)) k).left := by
    intro k; fin_cases k <;> rfl
  have hA : ∏ p : Fin 4 × Fin 3, h (D₂.famφB χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b p.2) ^
      (DegPre.famε 1 p.1 * GlobalTheory.MumCmp.twε p.2) =
      ∏ k : Fin 4, (h (((![𝟙 D₂.P.A, 𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂), toUnit D₂.P.A ≫ D₂.c χ₂, 1] :
        Fin 4 → (D₂.P.A ⟶ D₂.P.A)) k ≫ β) * (toUnit D₂.P.A ≫ g.b)).left *
        (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left) ^ DegPre.famε 1 k := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← ht, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (DegPre.famε 1 k) (GlobalTheory.MumCmp.twε i), zpow_mul, hx]
  have hL1 : ∏ k, h (GlobalTheory.MumCmp.twφ D₂ D β g.b 0 ≫ D.famφB χ k) ^ DegPre.famε 1 k =
      h ((β * (toUnit D₂.P.A ≫ g.b)) * (toUnit D₂.P.A ≫ D.c χ)).left * (h (toUnit D₂.P.A ≫ D.c χ).left)⁻¹ *
        h (1 : D₂.P.A ⟶ D.P.A).left := by
    rw [Fin.prod_univ_four]
    show h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ 𝟙 D.P.A).left ^ (((1 : ℕ) : ℤ) - 1) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ (𝟙 D.P.A * (toUnit D.P.A ≫ D.c χ))).left ^ (1 : ℤ) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A ≫ D.c χ).left ^ (-1 : ℤ) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc (β * (toUnit D₂.P.A ≫ g.b)),
      ← Category.assoc (β * (toUnit D₂.P.A ≫ g.b)),
      toUnit_unique ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A) (toUnit D₂.P.A)]
    simp only [Nat.cast_one, sub_self, zpow_zero, _root_.one_mul, zpow_one, zpow_neg_one]
    rfl
  have hL2 : ∏ k, h ((toUnit D₂.P.A).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b χ k) ^ DegPre.gtε k =
      (h ((toUnit D₂.P.A ≫ D.c χ) * (toUnit D₂.P.A ≫ g.b)).left)⁻¹ * h (toUnit D₂.P.A ≫ D.c χ).left *
        h (toUnit D₂.P.A ≫ g.b).left * (h (1 : D₂.P.A ⟶ D.P.A).left)⁻¹ := by
    rw [Fin.prod_univ_four]
    show h (toUnit D₂.P.A ≫ ((toUnit (𝟙_ (Over (Sp R))) ≫ D.c χ) * g.b)).left ^ (-1 : ℤ) *
      h (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R))) ≫ D.c χ).left ^ (1 : ℤ) *
      h (toUnit D₂.P.A ≫ g.b).left ^ (1 : ℤ) *
      h (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R))) ≫ η[D.P.A]).left ^ (-1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc (toUnit D₂.P.A), ← Category.assoc (toUnit D₂.P.A),
      toUnit_unique (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R)))) (toUnit D₂.P.A)]
    simp only [zpow_one, zpow_neg_one]
    rfl
  have hL3 : ∏ k, h ((toUnit D₂.P.A).left ≫ (![g.b.left, η[D.P.A].left] : Fin 2 → _) k) ^ (![-1, 1] : Fin 2 → ℤ) k =
      (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left := by
    rw [Fin.prod_univ_two]
    show h (toUnit D₂.P.A ≫ g.b).left ^ (-1 : ℤ) * h (toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [zpow_one, zpow_neg_one]
    rfl
  have h0 : (𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂)) ≫ β = β * (toUnit D₂.P.A ≫ D.c χ) := by
    rw [MonObj.mul_comp, Category.id_comp, Category.assoc, hc]
  have h2 : (toUnit D₂.P.A ≫ D₂.c χ₂) ≫ β = toUnit D₂.P.A ≫ D.c χ := by rw [Category.assoc, hc]
  have h3 : (1 : D₂.P.A ⟶ D₂.P.A) ≫ β = 1 := MonObj.one_comp β
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hL1, hL2, hL3, hA, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Category.id_comp, h0, h2, h3, _root_.one_mul]
  rw [mul_right_comm β (toUnit D₂.P.A ≫ D.c χ)]
  simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Nat.cast_one, sub_self, zpow_zero, zpow_neg, zpow_one, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem exists_translated_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A), IsMonHom β → ∀ (g : GtPt D (𝟙_ (Over (Sp R)))) (xe : D₂.X ≃+ D.X), (∀ χ : D₂.X, D₂.c χ ≫ β = D.c (xe χ)) → ∀ w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen → ∀ f : ∀ α : D.X, D.SecB 1 α, ∃ f₂ : ∀ α : D₂.X, D₂.SecB 1 α, ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i)) (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  intro R _ _ D D₂ β hβ g xe hc w hw ν hν f
  have key : ∀ χ : D₂.X, ∃ f₂ : D₂.SecB 1 χ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z)
      (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι),
      Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' →
      Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J *
        (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
      (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i))
        (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval f₂ r z J' := by
    intro χ
    haveI := hβ
    let u := LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.s (xe χ)) (toUnit D₂.P.A).left)
      (LB.pullGen D.P.L _ _ ν (toUnit D₂.P.A).left)
    have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (g.isGen _) _)
      (DVR.pullGen_isGen _ _ _ _ hν _)
    let S := pullMulSec (f (xe χ)) (GlobalTheory.MumCmp.twφ D₂ D β g.b 0) u hu
    obtain ⟨S', hS'⟩ := exists_sec D.P.isLB (formEq_coef D D₂ β g χ (xe χ) (hc χ)) S
    obtain ⟨T, hT⟩ := exists_nestSec (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε (D₂.famφB χ) (DegPre.famε 1) S'
    have hA := LB.isLB_linComb D₂.P.isLB (D₂.famφB χ) (DegPre.famε 1)
    have hB := LB.isLB_linComb (LB.isLB_linComb D.P.isLB (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε)
      (D₂.famφB χ) (DegPre.famε 1)
    have hU := DVR.linCombIso_isGen w hw (D₂.famφB χ) (DegPre.famε 1)
    refine ⟨DVR.secOfIso (u := LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB,
      fun Z r z J J' hJ hJ' => ?_⟩
    have hJ'' : Good (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε) z
        (fun χ' j => J (χ' ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) := fun χ' => hJ.mem _ χ'
    have m₁ := hJ'.mem (D₂.famφB χ) r
    have m₂ := hJ''.mem (D₂.famφB χ) r
    have e1 : Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J *
        (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
        Geo.Tor.sval T r z (fun χ' j => J (χ' ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) := by
      rw [hT Z r z J hJ, hS' Z r z J hJ, sval_pullMulSec _ _ _ hu r z hJ, val_mul hJ, val_pull hJ, val_pull hJ]
    rw [e1]
    have e2 := DVR.ps_gs_secOfIso (LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB
      (fun k => J' (r ≫ D₂.famφB χ k)) (fun k j => J ((r ≫ D₂.famφB χ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) r z ⟨m₁, m₂⟩
    have e3 := DVR.ps_gm_linCombIso w (D₂.famφB χ) (DegPre.famε 1)
      ((fun k j => J ((r ≫ D₂.famφB χ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)), (fun k => J' (r ≫ D₂.famφB χ k))) r z ⟨m₂, m₁⟩
    rw [show Geo.Tor.sval (DVR.secOfIso (u := LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB) r z J' = _ from e2,
      e3]
    exact (Units.mul_inv_cancel_left _ _).symm
  choose f₂ hf₂ using key
  exact ⟨f₂, hf₂⟩

end GlobalTheory.MumCmp.TrCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaValueSubsingletonBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistedThetaValue_subsingleton_base : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A), Subsingleton T.left → Odd m → N = m ^ 2 → τ.IsGen → x ^ N = 1 → h ^ m = β ≫ z₀ → ∃ v, IsTwVal P N m θ τ β x h v := by
  first | exact @GlobalTheory.UPoinc.USum.exists_isTwVal_of_subsingleton | exact GlobalTheory.UPoinc.USum.exists_isTwVal_of_subsingleton | (intros; apply GlobalTheory.UPoinc.USum.exists_isTwVal_of_subsingleton <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UnifEven

open GlobalTheory.UU GlobalTheory.LN

theorem isAdmissible_maximalIdeal_of_completeNormalCharZero {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) : admitted R (maximalIdeal R) := by
  refine ⟨hB.1, hB.1.2.2.2, hB.2, (maximalIdeal.isMaximal R).isPrime, ?_⟩
  letI := Ideal.Quotient.field (maximalIdeal R)
  infer_instance


set_option maxHeartbeats 1600000 in
theorem exists_setting {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (P : CP G) (hS : IsSemiAbelian G)
    (hE : EvenOn P) (A : PolAV (Sp (FractionRing R)))
    (gen : (Over.pullback (jK R)).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (g : R →+* V) (hg : Function.Injective g)
    (hc : (maximalIdeal V).comap g = maximalIdeal R) :
    ∃ (A' : PolAV (Sp (FractionRing V))) (s : HidaSetting V A' ((Over.pullback (spMap g)).obj G)) (w : _),
      IsCPMap s.P P (spMap g) (pullback.fst G.hom (spMap g)) pullback.condition w := by
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.lawsAndExpansions.1
  obtain ⟨X, _, _, _, Q₀, P₀, ⟨wl, hl⟩, hev⟩ := hE
  have := hS.smooth
  have := hS.geomConnected
  have := GlobalTheory.PreUnifLocal.isLocalRing_quot (maximalIdeal.isMaximal R).ne_top 0
  have hsm : Smooth (thickObj R (maximalIdeal R) 0 G).hom := by
    show Smooth (pullback.snd _ _); infer_instance
  have hgc : GeometricallyConnected (thickObj R (maximalIdeal R) 0 G).hom := by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  obtain ⟨D₀⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ hev
  let G' : Over (Sp V) := (Over.pullback (spMap g)).obj G
  have hS' : IsSemiAbelian G' := IsSemiAbelian.pullback _ G hS
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap g) G G' _ _ (toBase_mul_pullback G (spMap g)) P

  obtain ⟨ψ, sq'⟩ := ClosedPol.exists_generic_square g hg
  obtain ⟨A', gen', hgen', hA'⟩ := ClosedPol.exists_fibre_pull hL sq' P.L.isLB A gen hA
  rw [← hP'] at hA'
  obtain ⟨wA, hwA⟩ := hA'

  have le : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal V ^ (0 + 1)).comap g := by
    rw [zero_add, pow_one, pow_one, hc]
  let b : R ⧸ maximalIdeal R ^ (0 + 1) →+* V ⧸ maximalIdeal V ^ (0 + 1) :=
    Ideal.quotientMap (maximalIdeal V ^ (0 + 1)) g le
  have sq : spMap b ≫ thick R (maximalIdeal R) 0 = thick V (maximalIdeal V) 0 ≫ spMap g := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]
  obtain ⟨P₁, w₁, H₁⟩ := exists_isLevelCP (maximalIdeal V) 0 P'
  obtain ⟨F, pF, w₃, k₃⟩ := ClosedPol.exists_fourth (G := G) (G' := G') (H := thickObj R (maximalIdeal R) 0 G)
    (H' := thickObj V (maximalIdeal V) 0 G') (P := P) (P' := P') (N := P₀) (N' := P₁) sq
    (isGrpPullback_pullback G (spMap g)) (isGrpPullback_pullback G (thick R (maximalIdeal R) 0))
    (isGrpPullback_pullback _ (thick V (maximalIdeal V) 0)) H hl H₁
  obtain ⟨Q₁, D₁, -, -, -⟩ := ClosedPol.exists_desc_pull pF Q₀ D₀ k₃
  have ev := GlobalTheory.UniformizationSetting.exists_even_of_desc D₁
  exact ⟨A', ⟨hV, hS', gen', hgen', P', wA, hwA, X, Q₁, P₁, ⟨w₁, H₁⟩, ev⟩, wP, H⟩

end GlobalTheory.Mum.UnifEven


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mum.exists_unif_even : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → EvenOn P → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegData R (maximalIdeal R)) (U : Unif (maximalIdeal R) D A G), U.LG = P.L ∧ U.gen = gen := by
  intro R _ _ _ hB G _ _ P hS hEv A gen hgen hA
  obtain ⟨⟨hL, hL2, hL3, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hE := GlobalTheory.LN.ega_holds
  have hU := GlobalTheory.uniformisation_dvr_unconditional
  have hR := GlobalTheory.Mum.UnifEven.isAdmissible_maximalIdeal_of_completeNormalCharZero hB
  have := hR.1.1
  have := hR.2.2.1
  have hI := hR.2.2.2.1
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have := hV.1
  have hB' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hle : (maximalIdeal R).map φ ≤ maximalIdeal V := Ideal.map_le_iff_le_comap.2 hc.ge
  obtain ⟨D, U, rfl, rfl⟩ := _root_.GlobalTheory.Mum.exists_preU_even R hB G P hS hEv A gen hgen hA
  have hθ := _root_.GlobalTheory.Mum.thetaNZ_of_preU R hB D A G U hEv
  haveI := hgen
  obtain ⟨A', s, w, hw⟩ := GlobalTheory.Mum.UnifEven.exists_setting U.P hS hEv A U.gen hA hV φ hφ hc
  obtain ⟨D', U₀, hLG, -, -⟩ := hU V A' _ s
  obtain ⟨U', hU'⟩ := (GlobalTheory.LN.PreForm.under_exists_and_expands hL hL2 V _ D' A' _ s.semi).1 U₀.toUnifPre
  have := s.semi.smooth
  obtain ⟨w', hw'⟩ := GlobalTheory.PrimeUnif.isCPMap_of_eq hL.globalFns s.gen s.P U'.P (hU'.2.1.trans hLG) hw
  obtain ⟨C, -⟩ := _root_.GlobalTheory.LN.PreCompare.exists_cmp hL hL2 hE R V (maximalIdeal R) _ hR.1 hB' (maximalIdeal.isMaximal V).ne_top φ hle D _
    A A' G _ U U' _ (isGrpPullback_pullback G _) w' hw'
  obtain ⟨psi, h, Dd, hD, e, h₁, h₂, h₃⟩ := _root_.GlobalTheory.PsiRing.exists_degData_of_thetaNZ hL hL2 hE R (maximalIdeal R) hR V hV φ hφ hc D D' A A' G _
    U U' U₀ _ C hU' hθ
  obtain ⟨U₂, C₂, hD₂, eP, eg, k₁, k₂, k₃⟩ := GlobalTheory.PrimeUnif.exists_move psi h C hD Dd.toPre e h₁ h₂ h₃
  obtain ⟨U₁, -, hU₁, -⟩ := GlobalTheory.UnifDescent.exists_unif_of_cmp hL hL2 hE R V (maximalIdeal R) _ hR.1 hB' hI.ne_top φ hφ
    hle Dd D' A A' G _ U₂ U' U₀ _ C₂ hD₂ hU' k₁ k₂ k₃
  exact ⟨Dd, U₁, hU₁.2.1.symm.trans (congrArg GlobalTheory.UU.CP.L eP), hU₁.1.symm.trans eg⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverFiniteExtOfSymmetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_uCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))), (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (C : UCover R₁) (a : C.A.A.left ⟶ A.A.left), FinExt ρ ∧ IsFib ρ A C.A a := by
  intro R _ _ _ hR A hA
  obtain ⟨n, hn, hno, hnu⟩ := _root_.GlobalTheory.exists_odd_prime_isUnit_of_base R hR
  obtain ⟨k, j, hk, hj, hbig⟩ := _root_.GlobalTheory.Mum.bigSizes A.g n hn hno
  have hmu : IsUnit (((n ^ j * (n ^ k) ^ 2) ^ 2 : ℕ) : R) := by
    push_cast; exact ((hnu.pow _).mul ((hnu.pow _).pow _)).pow _
  obtain ⟨R₁, _, _, _, ρ, A₁, a, ζ, lev, hfin, hfib, hg, hS⟩ :=
    GlobalTheory.T.exists_symplecticLevel_after_finiteExtension_base R hR A hA _ (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hn.ne_zero) (pow_ne_zero _ (pow_ne_zero _ hn.ne_zero))))) hmu
  haveI : CharZero R₁ := ⟨fun x y h => by
    have := hR.2
    exact Nat.cast_injective (hfin.2.1 (by simpa using h))⟩
  have hnu₁ : IsUnit (n : R₁) := by simpa using hnu.map ρ
  obtain ⟨o, Ω, _, _, _, _, S, ρS, b, e, φ, hSg, hSN, hSr, hb, hcart, hlb⟩ :=
    GlobalTheory.T.exists_thetaSystem_spread_of_level_fractionField R₁ A₁ hS n k j hn hno hk hj hnu₁ ζ lev
  have hB : S.Big := hbig o Ω S (hSg.trans hg) hSN hSr
  obtain ⟨J₀, _, t₀, ht₀, hfin'⟩ := _root_.GlobalTheory.ZH.thetaSys_gen_tuple o Ω S
  obtain ⟨M, U₀, EE, hO, -, -, ⟨Z⟩⟩ := GlobalTheory.zhSt_holds o Ω S ρS hB J₀ t₀ ht₀ hfin'
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.Mum.exists_uCover_of_zhOut R₁ o Ω S ρS M U₀ EE hO Z b e hb A₁ φ hcart hlb
  subst hC
  exact ⟨R₁, _, _, _, ρ, C, a, hfin, hfib⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupGaloisAutomorphismMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gal_map_maximalIdeal_le {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R'] {ρ : R →+* R'} (σ : Gal ρ) :
    (maximalIdeal R').map (Gal.hom σ) ≤ maximalIdeal R' := by
  refine Ideal.map_le_of_le_comap fun x hx => ?_
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply (mem_nonunits_iff.1 ((mem_maximalIdeal x).1 hx))
  have := hu.map (σ.1.symm : R' ≃+* R')
  simpa [Gal.hom] using this

theorem exists_galMap : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ), ∃ a, GalMap hD U' σ a := by
  intro R _ _ _ _ R' _ _ _ ρ hρ D D' hD A' G' _ _ hG' U' σ
  obtain ⟨hR', hinj, -⟩ := hρ
  have hσi : Function.Injective (Gal.hom σ) := σ.1.injective
  obtain ⟨h, hPO⟩ := _root_.GlobalTheory.Mum.SelfPull.exists_isPullDeg_self_pullOver R R' ρ hinj D.toPre D'.toPre hD σ
  obtain ⟨A'', U'', hU''⟩ := _root_.GlobalTheory.Mum.UnifPull.exists_pull_of_deg R' R' _ _ hR' hR' (Gal.hom σ) hσi (gal_map_maximalIdeal_le σ) D' D' h A' G'
    hG' U'
  obtain ⟨hid, hxe, hem⟩ := _root_.GlobalTheory.DegPullId.exists_isPullDeg_id_self R' _ hR' D'
  have hsa : IsSemiAbelian ((Over.pullback (specOf (Gal.hom σ))).obj G') := IsSemiAbelian.pullback _ G' hG'
  obtain ⟨-, bc1, -, -, mbc1, -, hU1, -⟩ :=
    _root_.GlobalTheory.unif_determined_by_data_normal R' hR' D' A'' ((Over.pullback (specOf (Gal.hom σ))).obj G') hsa U'' D' A' G' hG' U' hid
  obtain ⟨h', bc, hU, hxe', hem', -, hmon⟩ := _root_.GlobalTheory.PullUnifId.isPullUnif_comp_id R' R' _ _ (Gal.hom σ) D' D' D' h hid A' A'' A' G'
    ((Over.pullback (specOf (Gal.hom σ))).obj G') G' (Iso.refl _) bc1 U' U'' U' hU'' hU1
  haveI : IsMonHom bc.hom := hmon (by show IsMonHom (𝟙 _); infer_instance) mbc1
  refine ⟨bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)), ?_, h', bc, rfl, hU, ?_⟩
  · exact ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G' (spMap (Gal.hom σ)))).congr (Category.id_comp _) rfl
  · refine ⟨fun x => by rw [hxe', hxe]; exact hPO.1 x, fun b c hb hc => ?_⟩
    rw [hc, hem', reassoc_of% hem]
    exact hPO.2 b _ hb rfl

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePointOfLevelLiftHarrisTaylor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.OfLift

theorem exists_objMap_comp {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
    {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

def ObjMap.forget {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N' : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N' s'} {o : Obj b N' s} {f : S' ⟶ S}
    (m : ObjMap o' o f) (N : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) : ObjMap (o'.forget N hd hc) (o.forget N hd hc) f :=
  ⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, fun y => m.eta _⟩

theorem ofLift : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), 3 ≤ N → ∀ (hd : N ∣ N') (hc : N'.Coprime p) (M : Model b N) (M' : Model b N') (π : M'.X ⟶ M.X), π ≫ M.s = M'.s → ∀ (om : ObjMap (M'.univ.forget N hd hc) M.univ π) (T : Over M.X) (lv : D.La → (T ⟶ M.univ.A)), IsLift M.univ N' T lv → ∃ g : T.left ⟶ M'.X, g ≫ π = T.hom ∧ ∀ a, (lv a).left = g ≫ (M'.univ.eta a).left ≫ om.φ := by
  intro p _ D R _ b N N' hN hd hc M M' π hπ om T lv hlv
  obtain ⟨o'', mm, hmm⟩ := _root_.GlobalTheory.HTLift.exists_obj_of_isLift p D R b N N' hd hc M.X M.s M.univ T lv hlv
  obtain ⟨g, ⟨hg, ⟨m''⟩⟩, -⟩ := M'.rep T.left (T.hom ≫ M.s) o''
  obtain ⟨c, hcφ⟩ := exists_objMap_comp (ObjMap.forget m'' N hd hc) om
  have hNp : N.Coprime p := Nat.Coprime.coprime_dvd_left hd hc
  have hgπ : g ≫ π = T.hom := by
    obtain ⟨f, -, hu⟩ := M.rep T.left (T.hom ≫ M.s) (o''.forget N hd hc)
    have e1 := hu (g ≫ π) ⟨by rw [Category.assoc, hπ, hg], ⟨c⟩⟩
    have e2 := hu T.hom ⟨rfl, ⟨mm⟩⟩
    exact e1.trans e2.symm
  have hφ : c.φ = mm.φ := _root_.GlobalTheory.UPel.HT.Rigid.objMap_phi_unique p D R b N hN hNp M.X T.left M.s (T.hom ≫ M.s) M.univ (o''.forget N hd hc) _ _ c mm hgπ
  refine ⟨g, hgπ, fun a => ?_⟩
  rw [← hmm a, ← hφ, hcφ]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ om.φ) (m''.eta a)).trans (Category.assoc _ _ _))

end GlobalTheory.UPel.HT.OfLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePushoutTorsorSectionMulDifferenceStatement
section
theorem GlobalTheory.T.existsUnique_pushoutTorsorSection_mul_difference :
    type_of% @GlobalTheory.sec_mul_diff :=
  @GlobalTheory.sec_mul_diff
end

