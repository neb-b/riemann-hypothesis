module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionalPosOnSquaresEqSumOfSquares
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.SumSqFunctional

open Matrix

def quadR {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * (L i j : ℝ) * v j

lemma quadR_eq {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℝ) :
    star v ⬝ᵥ (L.map (Int.cast : ℤ → ℝ)) *ᵥ v = quadR L v := by
  simp [quadR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

lemma quadR_intCast {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (w : Fin r → ℤ) :
    quadR L (fun i => (w i : ℝ)) = ((w ⬝ᵥ L *ᵥ w : ℤ) : ℝ) := by
  simp [quadR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

lemma continuous_quadR {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) : Continuous (quadR L) := by
  unfold quadR; fun_prop

lemma exists_int_multiple {r : ℕ} (q : Fin r → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ w : Fin r → ℤ, ∀ i, (w i : ℚ) = d * q i := by
  refine ⟨∏ i, (q i).den, Finset.prod_pos (fun i _ => (q i).den_pos), ?_⟩
  have : ∀ i, ∃ z : ℤ, (z : ℚ) = ((∏ j, (q j).den : ℕ) : ℚ) * q i := by
    intro i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
    refine ⟨k * (q i).num, ?_⟩
    rw [hk]; push_cast
    rw [mul_comm ((q i).den : ℚ) (k : ℚ), mul_assoc, Rat.den_mul_eq_num]
  choose w hw using this
  exact ⟨w, hw⟩

lemma quadR_pos_rat {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ)
    (hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v) (q : Fin r → ℚ) (hq : q ≠ 0) :
    0 < quadR L (fun i => (q i : ℝ)) := by
  obtain ⟨d, hd, w, hw⟩ := exists_int_multiple q
  have hwR : ∀ i, (w i : ℝ) = d * (q i : ℝ) := by
    intro i; have := congrArg (Rat.cast : ℚ → ℝ) (hw i); push_cast at this; exact this
  have hw0 : w ≠ 0 := by
    intro h; apply hq; funext i
    have := hw i; rw [h] at this; simp at this
    rcases this with h1 | h1
    · exact absurd h1 (by exact_mod_cast hd.ne')
    · exact h1
  have h1 := hp w hw0
  have h2 : quadR L (fun i => (w i : ℝ)) = (d : ℝ) ^ 2 * quadR L (fun i => (q i : ℝ)) := by
    simp only [quadR, hwR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h3 : 0 < quadR L (fun i => (w i : ℝ)) := by
    rw [quadR_intCast]; exact_mod_cast h1
  rw [h2] at h3
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  exact pos_of_mul_pos_right h3 hd2.le

lemma quadR_nonneg {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ)
    (hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v) (x : Fin r → ℝ) : 0 ≤ quadR L x := by
  have hdense : DenseRange (Pi.map (fun (_ : Fin r) (t : ℚ) => (t : ℝ))) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hcl : IsClosed {x : Fin r → ℝ | 0 ≤ quadR L x} :=
    isClosed_le continuous_const (continuous_quadR L)
  have hsub : Set.range (Pi.map (fun (_ : Fin r) (t : ℚ) => (t : ℝ))) ⊆ {x | 0 ≤ quadR L x} := by
    rintro _ ⟨q, rfl⟩
    by_cases hq : q = 0
    · subst hq; simp [quadR]
    · exact (quadR_pos_rat L hp q hq).le
  have := hcl.closure_subset_iff.mpr hsub
  rw [hdense.closure_range] at this
  exact this (Set.mem_univ x)

theorem posDef_of_pos_int {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (hs : Lᵀ = L)
    (hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v) :
    (L.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hH : (L.map (Int.cast : ℤ → ℝ)).IsHermitian := by
    ext i j
    have := congrFun (congrFun hs j) i
    simp only [Matrix.transpose_apply] at this
    simp [Matrix.conjTranspose_apply, this]
  have hPSD : (L.map (Int.cast : ℤ → ℝ)).PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH (fun x => by
      rw [quadR_eq]; exact quadR_nonneg L hp x)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH (fun x hx => ?_)
  rw [quadR_eq]
  refine lt_of_le_of_ne (quadR_nonneg L hp x) (fun h0 => ?_)
  have hz : (L.map (Int.cast : ℤ → ℝ)) *ᵥ x = 0 := by
    rw [← hPSD.dotProduct_mulVec_zero_iff, quadR_eq]; exact h0.symm
  have hdetR : (L.map (Int.cast : ℤ → ℝ)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hz⟩
  have hdet : L.det = 0 := by
    have := (Int.castRingHom ℝ).map_det L
    rw [RingHom.mapMatrix_apply] at this
    simp only [eq_intCast] at this
    have h' : ((L.det : ℤ) : ℝ) = 0 := by rw [this]; exact hdetR
    exact_mod_cast h'
  obtain ⟨w, hw, hLw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have := hp w hw
  rw [hLw, dotProduct_zero] at this
  exact lt_irrefl _ this

end GlobalTheory.Poinc.SumSqFunctional

namespace GlobalTheory.Poinc.SumSqFunctional

open Matrix

theorem sumsq_functional : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), (∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → 0 < lam (GlobalTheory.PolFan.sqForm l)) → ∃ (D m : ℕ) (a : Fin m → X), 1 ≤ D ∧ Submodule.span ℤ (Set.range a) = ⊤ ∧ ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → ∑ i, β (a i) (a i) = (D : ℤ) * lam β := by
  intro X _ _ _ lam hpos
  let b : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ X))) ℤ X :=
    (Module.Free.chooseBasis ℤ X).reindex (Fintype.equivFin _)
  set r := Fintype.card (Module.Free.ChooseBasisIndex ℤ X)
  let C : Fin r → Fin r → LinearMap.BilinForm ℤ X := fun i j =>
    (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)
  have hexp : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (b i) (b j) • C i j := by
    intro β
    refine b.ext fun k => b.ext fun l => ?_
    simp [C, LinearMap.sum_apply, Finsupp.single_apply]
  have hbil : ∀ (β : LinearMap.BilinForm ℤ X) (c d : Fin r → ℤ),
      β (∑ i, c i • b i) (∑ j, d j • b j) = ∑ i, ∑ j, c i * d j * β (b i) (b j) := by
    intro β c d
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, LinearMap.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    rw [Finset.sum_comm]
  let L : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => lam (C i j) + lam (C j i)
  have hlam : ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) →
      2 * lam β = ∑ i, ∑ j, L i j * β (b i) (b j) := by
    intro β hβ
    have h1 : lam β = ∑ i, ∑ j, β (b i) (b j) * lam (C i j) := by
      conv_lhs => rw [hexp β]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, map_smul]
    have h2 : lam β = ∑ i, ∑ j, β (b i) (b j) * lam (C j i) := by
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hβ]
    calc 2 * lam β = lam β + lam β := by ring
      _ = _ := by
        nth_rewrite 1 [h1]
        rw [h2]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [L, Matrix.of_apply]; ring
  have hs : Lᵀ = L := by
    ext i j; simp [L, add_comm]
  have hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v := by
    intro v hv
    let l : X →ₗ[ℤ] ℤ := ∑ i, v i • b.coord i
    have hl : ∀ k, l (b k) = v k := by
      intro k; simp [l, Finsupp.single_apply]
    have hl0 : l ≠ 0 := by
      intro h; apply hv; funext k; rw [← hl k, h]; rfl
    have hsq : ∀ x y, GlobalTheory.PolFan.sqForm l x y = l x * l y := by
      intro x y; simp [GlobalTheory.PolFan.sqForm]
    have hsym : ∀ x y, GlobalTheory.PolFan.sqForm l x y = GlobalTheory.PolFan.sqForm l y x := by
      intro x y; rw [hsq, hsq, mul_comm]
    have h2 := hlam _ hsym
    have h3 : v ⬝ᵥ L *ᵥ v = 2 * lam (GlobalTheory.PolFan.sqForm l) := by
      rw [h2]
      simp only [hsq, hl, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h3]; have := hpos l hl0; omega
  have hPD := posDef_of_pos_int L hs hp
  obtain ⟨D, m, a', hD, hspan, hsum⟩ := GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span r L hPD
  have hentry : ∀ i j, (D : ℤ) * L i j = ∑ k, a' k i * a' k j := by
    intro i j
    have := congrFun (congrFun hsum i) j
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
  refine ⟨2 * D, m, fun k => ∑ i, a' k i • b i, by omega, ?_, ?_⟩
  · have hfun : (fun k => ∑ i, a' k i • b i) = ⇑b.equivFun.symm.toLinearMap ∘ a' := by
      funext k; simp [Module.Basis.equivFun_symm_apply]
    rw [hfun, Set.range_comp, Submodule.span_image, hspan, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr b.equivFun.symm.surjective
  · intro β hβ
    simp only [hbil]
    rw [Finset.sum_comm]
    have : ∀ i, (∑ y, ∑ x, a' y i * a' y x * β (b i) (b x)) = ∑ j, (D : ℤ) * L i j * β (b i) (b j) := by
      intro i
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hentry, Finset.sum_mul]
    simp only [this]
    have h2 := hlam β hβ
    push_cast
    rw [mul_comm 2 (D : ℤ), mul_assoc, h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.Poinc.SumSqFunctional
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValueLinCombChangeOfCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem valR_linComb_g_factor {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι)
    (hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) (k : K) :
    valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      ((res (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
      (inf_le_right.trans (LB.wchart_le L φ j' k)) :
        LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
      (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (ε k)).val = trV L (y ≫ φ k) (j k) (j' k) (ε k) := by
  have h0 : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L φ j k)) (inf_le_right.trans (LB.wchart_le L φ j' k))
  have key : (res h0 (pullU (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)))) ^ (ε k) =
      res h0 (pullU (φ k) (L.U (j k) ⊓ L.U (j' k)) ((L.g (j k) (j' k)) ^ (ε k))) :=
    ((congrArg (res h0) (map_zpow (pullU (φ k) (L.U (j k) ⊓ L.U (j' k))) _ _)).trans
      (map_zpow (res h0) _ _)).symm
  refine (congrArg (fun u => valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val u)) key).trans ?_
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y h0 hh
      (((φ k).app (L.U (j k) ⊓ L.U (j' k))).hom ((L.g (j k) (j' k)) ^ (ε k)).val)
  refine Eq.trans ?_ (e1.trans ?_)
  · rfl
  · unfold trV
    exact GlobalTheory.ZH.EvCrd.valR_comp y (φ k) _ (hh.trans (y.preimage_mono h0)) _

theorem valR_gen_linComb : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (t.s j).val =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (t.s j').val := by
  intro X Y L K _ φ ε t ht A _ y j j' h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun q hq => ⟨h hq, h' hq⟩
  have e : valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      (res (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) (t.s j)).val =
      valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      ((show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val *
        (res (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') (t.s j')).val) :=
    congrArg (fun u => valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val u)) (ht j j')
  rw [GlobalTheory.ZH.CrdCalc.valR_mul y _ hh] at e
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) hh (t.s j).val
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') hh (t.s j').val
  have e3 : valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val =
      ∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k) := by
    change valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val (∏ k, _)) = _
    rw [Units.coe_prod, GlobalTheory.ZH.CrdCalc.valR_eq y _ hh, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← GlobalTheory.ZH.CrdCalc.valR_eq y _ hh]
    exact valR_linComb_g_factor L φ ε y j j' hh k
  rw [← e3]
  exact e1.symm.trans (e.trans (congrArg _ e2))

end GlobalTheory.MBLow.TanGauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericTangentCoefficientsUniqueAffineOpenBasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv.GenUniq

open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)

attribute [local instance] Over.cartesianMonoidalCategory

theorem dualMap_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective (Formalism.L2.Pj.dualMap f) := by
  intro a b h
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp only [Formalism.L2.Pj.dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add] at h1 h2
  exact TrivSqZeroExt.ext (hf h1) (hf h2)

theorem exists_common_denom {A K : Type} [CommRing A] [Field K] (ρ : A →+* K)
    (hfr : ∀ x : K, ∃ a b : A, ρ b ≠ 0 ∧ x * ρ b = ρ a) {κ : Type} [Fintype κ] (c : κ → K) :
    ∃ (b : A) (a : κ → A), ρ b ≠ 0 ∧ ∀ i, ρ b * c i = ρ (a i) := by
  classical
  choose a b hb hab using hfr
  refine ⟨∏ i, b (c i), fun i => a (c i) * ∏ j ∈ Finset.univ.erase i, b (c j), ?_, fun i => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hb _
  · rw [← Finset.mul_prod_erase Finset.univ (fun j => b (c j)) (Finset.mem_univ i), map_mul, map_mul, ← hab]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def bcEps {A K : Type} [CommRing A] [CommRing K] (ρ : A →+* K) (x : Sp A ⟶ X) :
    tEpsG (spMap ρ ≫ x) ⟶ tEpsG x :=
  Over.homMk (spMap (Formalism.L2.Pj.dualMap ρ)) (by
    show spMap (Formalism.L2.Pj.dualMap ρ) ≫ spMap (algebraMap A (DualNumber A)) ≫ x =
      spMap (algebraMap K (DualNumber K)) ≫ spMap ρ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, Formalism.L2.Pj.dualMap_comp_alg])

theorem bcEps_smT {A K : Type} [CommRing A] [CommRing K] (ρ : A →+* K) (x : Sp A ⟶ X) (a : A)
    (v : tEpsG x ⟶ t.G) :
    bcEps ρ x ≫ smT x a v = smT (spMap ρ ≫ x) (ρ a) (bcEps ρ x ≫ v) := by
  apply Over.OverMorphism.ext
  show spMap (Formalism.L2.Pj.dualMap ρ) ≫ spMap (epsMul a) ≫ v.left =
    spMap (epsMul (ρ a)) ≫ spMap (Formalism.L2.Pj.dualMap ρ) ≫ v.left
  rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, Formalism.L2.Pj.dualMap_comp_epsMul]

theorem bcEps_combT {A K : Type} [CommRing A] [CommRing K] (ρ : A →+* K) (x : Sp A ⟶ X) {n : ℕ}
    (v : Fin n → (tEpsG x ⟶ t.G)) (a : Fin n → A) :
    bcEps ρ x ≫ combT x v a = combT (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ v i) (fun i => ρ (a i)) := by
  let f : (tEpsG x ⟶ t.G) →* (tEpsG (spMap ρ ≫ x) ⟶ t.G) :=
    { toFun := fun u => bcEps ρ x ≫ u
      map_one' := MonObj.comp_one _
      map_mul' := fun u w => MonObj.comp_mul _ _ _ }
  have h := map_prod f (fun j => smT x (a j) (v j)) Finset.univ
  refine h.trans ?_
  exact Finset.prod_congr rfl fun i _ => bcEps_smT t ρ x (a i) (v i)

theorem coeff_unique {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hinj : Function.Injective ρ)
    (hfr : ∀ x : K, ∃ a b : A, ρ b ≠ 0 ∧ x * ρ b = ρ a) (x : Sp A ⟶ X) {n : ℕ}
    (v : Fin n → (Sp (DualNumber A) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf : Fin n → A, IsCombAtG t x v cf w)
    (cf cf' : Fin n → K) (w : Sp (DualNumber K) ⟶ t.G.left)
    (h : IsCombAtG t (spMap ρ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap ρ) ≫ v i) cf w)
    (h' : IsCombAtG t (spMap ρ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap ρ) ≫ v i) cf' w) : cf = cf' := by
  let V : Fin n → (tEpsG x ⟶ t.G) := fun i => ovT (hv i)
  have e := (isCombAtG_iff t (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf w).1 h
  have e' := (isCombAtG_iff t (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf' w).1 h'
  have hc : combT (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf =
      combT (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf' := Over.OverMorphism.ext (e.trans e'.symm)
  obtain ⟨b, a, hb0, ha⟩ := exists_common_denom ρ hfr (Sum.elim cf cf')
  have hs := congrArg (smT (spMap ρ ≫ x) (ρ b)) hc
  rw [smT_combT, smT_combT] at hs
  have a1 : (fun j => ρ b * cf j) = fun j => ρ (a (Sum.inl j)) := funext fun j => ha (Sum.inl j)
  have a2 : (fun j => ρ b * cf' j) = fun j => ρ (a (Sum.inr j)) := funext fun j => ha (Sum.inr j)
  rw [a1, a2, ← bcEps_combT, ← bcEps_combT] at hs
  have hsep : IsSeparated t.G.hom := t.semi.separated
  have hdom : IsSchemeTheoreticallyDominant (spMap (Formalism.L2.Pj.dualMap ρ)) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom _) (dualMap_injective ρ hinj)
  have hA : (combT x V fun j => a (Sum.inl j)).left = (combT x V fun j => a (Sum.inr j)).left :=
    GlobalTheory.ExtUnique.hom_ext_of_dominant t.G.hom
      ((Over.w (combT x V fun j => a (Sum.inl j))).trans (Over.w (combT x V fun j => a (Sum.inr j))).symm)
      (spMap (Formalism.L2.Pj.dualMap ρ)) (congrArg (fun φ => φ.left) hs)
  have ht : IsTanAtG t x (combT x V fun j => a (Sum.inl j)).left :=
    isTanAtG_of _ (combT_tan x V (fun j => smT_zero_ovT (hv j)) _)
  have haa : (fun j => a (Sum.inl j)) = fun j => a (Sum.inr j) :=
    (hb _ ht).unique ((isCombAtG_iff t x V _ _).2 rfl) ((isCombAtG_iff t x V _ _).2 hA.symm)
  funext j
  apply mul_left_cancel₀ hb0
  rw [congrFun a1 j, congrFun a2 j, congrFun haa j]

end GlobalTheory.LogKSDiv.GenUniq

namespace GlobalTheory.LogKSDiv

theorem generic_coeff_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (W : X.affineOpens) (K : Type) [Field K] (ρW : Γ(X, W.1) →+* K), Function.Injective ρW → (∀ x : K, ∃ a b : Γ(X, W.1), ρW b ≠ 0 ∧ x * ρW b = ρW a) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, W.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart W) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart W) w → ∃! cf : Fin n → Γ(X, W.1), IsCombAtG t (GlobalTheory.LogKS.chart W) v cf w) → ∀ (cf cf' : Fin n → K) (w : Sp (DualNumber K) ⟶ t.G.left), IsCombAtG t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (fun i => spMap (Formalism.L2.Pj.dualMap ρW) ≫ v i) cf w → IsCombAtG t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (fun i => spMap (Formalism.L2.Pj.dualMap ρW) ≫ v i) cf' w → cf = cf' :=
  fun _ _ _ _ _ _ t W _ _ ρW hinj hfr _ v hv hb cf cf' w h h' =>
    GenUniq.coeff_unique t ρW hinj hfr (GlobalTheory.LogKS.chart W) v hv hb cf cf' w h h'

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOfIsOpenImmersionCompSurjec
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem geometricallyIntegral_of_isOpenImmersion_comp_surjective :
    ∀ (O Z T : Scheme.{0}) (j : O ⟶ Z) (f : Z ⟶ T) [IsOpenImmersion j] [GeometricallyIntegral f], Surjective (j ≫ f) → GeometricallyIntegral (j ≫ f) := by
  intro O Z T j f _ _ hs
  refine ⟨fun {K} _ y P fst snd h => ?_⟩
  have hZf : IsIntegral (pullback f y) :=
    GeometricallyIntegral.geometrically_isIntegral (f := f) y _ _ (IsPullback.of_hasPullback f y)
  let fst' : P ⟶ pullback f y := pullback.lift (fst ≫ j) snd (by rw [Category.assoc]; exact h.w)
  have sq : IsPullback fst fst' j (pullback.fst f y) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd f y) (v₂₂ := f) (h₃₁ := y) ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback f y)
    have e : fst' ≫ pullback.snd f y = snd := pullback.lift_snd _ _ _
    rw [e]; exact h
  have : IsOpenImmersion fst' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq inferInstance
  have hsn : Surjective snd := MorphismProperty.of_isPullback (P := @Surjective) h hs
  have : Nonempty P := by
    obtain ⟨z, -⟩ := snd.surjective (Nonempty.some inferInstance : Spec (.of K))
    exact ⟨z⟩
  exact isIntegral_of_isOpenImmersion fst'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermOriginConstantSectionEqOriginStalkConstants
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GermConst

theorem germ_constFn_origin : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (O : G.left.Opens) (hO : origin G ∈ O) (r : R), (G.left.presheaf.germ O (origin G) hO).hom (constFn G.hom O r) = constO G r := by
  intro R _ _ G _ O hO r
  have e := Scheme.Hom.appLE_map G.hom (U := ⊤) (V := ⊤) (fun _ _ => trivial) (homOfLE (le_top : O ≤ ⊤)).op
  have h : constFn G.hom O r = (G.left.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom (constFn G.hom ⊤ r) := by
    unfold constFn
    rw [← e]
    rfl
  rw [h, TopCat.Presheaf.germ_res_apply]
  rfl

end GlobalTheory.GermConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodOfFiniteSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FiniteSurjDim

theorem eq_of_finite_surjective {k : Type} [Field k] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (p : Y ⟶ Spec (CommRingCat.of k)) [Nonempty X] {a b : ℕ} (ha : SmoothOfRelativeDimension a (f ≫ p))
    (hb : SmoothOfRelativeDimension b p) : a = b := by
  have : Nonempty Y := ⟨f (Classical.arbitrary X)⟩
  have h1 := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (f ≫ p) a ha
  have h2 := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p b hb
  have c1 : topologicalKrullDim Y ≤ topologicalKrullDim X :=
    GlobalTheory.PosBaseChange.dim_le_of_isClosedMap f.isClosedMap f.surjective
  have c2 : topologicalKrullDim X ≤ topologicalKrullDim Y :=
    GlobalTheory.PosBaseChange.dim_le_of_isDiscrete f.continuous fun y => f.isDiscrete_preimage_singleton y
  rw [h1, h2] at c1 c2
  exact_mod_cast le_antisymm c2 c1

end GlobalTheory.FiniteSurjDim
end

