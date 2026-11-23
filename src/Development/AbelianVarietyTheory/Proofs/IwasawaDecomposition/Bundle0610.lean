module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStarDepthSetThroughRadicalFreePresentation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellLeastDimVanishesWhereFormVanishesDiagonal
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

noncomputable section

namespace GlobalTheory.PolFan.Mark

theorem exists_zsmul_mem_of_finrank_le_of_le {M : Type} [AddCommGroup M] {N L : Submodule ℤ M}
    [Module.Finite ℤ L] (hNL : N ≤ L) (hr : Module.finrank ℤ L ≤ Module.finrank ℤ N) {x : M} (hx : x ∈ L) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ N := by
  have h1 := Submodule.finrank_quotient_add_finrank (N.comap L.subtype)
  have h2 : Module.finrank ℤ (N.comap L.subtype) = Module.finrank ℤ N :=
    (Submodule.comapSubtypeEquivOfLe hNL).finrank_eq
  have h0 : Module.finrank ℤ (L ⧸ N.comap L.subtype) = 0 := by omega
  obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff.1 h0) (Submodule.Quotient.mk ⟨x, hx⟩)
  refine ⟨a, ha, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  exact hax

theorem vanish_of_inRCone_of_genRank_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (τ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ τ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone τ β → (genRank τ : ℝ) ≤ lab.evalZ β → ∀ j y, β y y = 0 → τ j y y = 0 := by
  intro E _ _ _ H q ψ lab hψ hlab X _ _ _ _ hX hdom m τ hτ β hβ hβp hβc hrk j y hy
  classical
  let P : Fin m → Prop := fun j => ∀ y, β y y = 0 → τ j y y = 0
  have hw : ∀ j, ∃ y, β y y = 0 ∧ (¬ P j → 0 < τ j y y) := by
    intro j
    by_cases hj : P j
    · exact ⟨0, by simp, fun h => (h hj).elim⟩
    · simp only [P, not_forall] at hj
      obtain ⟨y, hy, hne⟩ := hj
      exact ⟨y, hy, fun _ => lt_of_le_of_ne (hτ.nonneg j y) (Ne.symm hne)⟩
  choose w hw0 hwpos using hw
  let T : Finset (Fin m) := Finset.univ.filter P
  let s : Fin T.card ↪ Fin m := (T.orderEmbOfFin rfl).toEmbedding
  have hsr : Set.range s = ↑T := Finset.range_orderEmbOfFin T rfl
  have hP : ∀ k, P k ↔ k ∈ Set.range s := fun k => by rw [hsr]; simp [T]
  let hf : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ∑ i, LinearMap.applyₗ (w i) ∘ₗ LinearMap.applyₗ (w i)
  have hfa : ∀ x : LinearMap.BilinForm ℤ X, hf x = ∑ i, x (w i) (w i) := fun x => by
    simp [hf, LinearMap.sum_apply]
  have hcut : IsFaceCut τ s hf := by
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rw [hfa]; exact Finset.sum_nonneg fun i _ => hτ.nonneg k (w i)
    · rw [← hP, hfa]
      constructor
      · intro h0
        by_contra hk
        have h1 : τ k (w k) (w k) ≤ ∑ i, τ k (w i) (w i) :=
          Finset.single_le_sum (f := fun i => τ k (w i) (w i)) (fun i _ => hτ.nonneg k (w i)) (Finset.mem_univ k)
        have h2 := hwpos k hk
        omega
      · intro hk
        exact Finset.sum_eq_zero fun i _ => hk _ (hw0 i)
  have hcell : IsCell H.bar ψ (fun k => τ (s k)) :=
    isCell_face_of_isFaceCut E H q ψ hψ X hX hdom m τ hτ _ s hf hcut
  obtain ⟨c, hc, hce⟩ := hβc
  have hc0 : ∀ i, ¬ P i → c i = 0 := by
    intro i hi
    have e : (β (w i) (w i) : ℝ) = ∑ k, c k * (τ k (w i) (w i) : ℝ) := by
      have := LinearMap.congr_fun₂ hce (w i) (w i)
      simpa [LinearMap.sum_apply] using this
    rw [hw0 i, Int.cast_zero] at e
    have h1 : c i * (τ i (w i) (w i) : ℝ) ≤ ∑ k, c k * (τ k (w i) (w i) : ℝ) :=
      Finset.single_le_sum (f := fun k => c k * (τ k (w i) (w i) : ℝ))
        (fun k _ => mul_nonneg (hc k) (by exact_mod_cast hτ.nonneg k (w i))) (Finset.mem_univ i)
    have h2 : (0 : ℝ) < τ i (w i) (w i) := by exact_mod_cast hwpos i hi
    rw [← e] at h1
    nlinarith [hc i]
  have hmap : Finset.univ.map s = T := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    rw [← Set.mem_range, ← hP]
    simp [T]
  have hcone : InRCone (fun k => τ (s k)) β := by
    refine ⟨fun k => c (s k), fun k => hc _, ?_⟩
    rw [hce]
    have e1 := Finset.sum_map Finset.univ s (fun i => c i • toReal (τ i))
    rw [hmap] at e1
    rw [← e1]
    refine (Finset.sum_subset (Finset.subset_univ T) fun i _ hi => ?_).symm
    rw [hc0 i (by simpa [T] using hi), zero_smul]
  have hl := hlab X hX β hβ hβp
  have hle : sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k} ≤ genRank (fun k => τ (s k)) := Nat.sInf_le ⟨_, _, hcell, hcone, rfl⟩
  have hrk' : genRank τ ≤ genRank (fun k => τ (s k)) := by
    rw [hl] at hrk
    have h4 : ((genRank τ : ℕ) : ℝ) ≤ ((genRank (fun k => τ (s k)) : ℕ) : ℝ) := hrk.trans (Nat.cast_le.2 hle)
    exact_mod_cast h4
  haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range τ)) := Module.Finite.span_of_finite ℤ (Set.finite_range τ)
  have hNL : Submodule.span ℤ (Set.range fun k => τ (s k)) ≤ Submodule.span ℤ (Set.range τ) :=
    Submodule.span_mono (Set.range_comp_subset_range s τ)
  obtain ⟨n, hn, hnmem⟩ := exists_zsmul_mem_of_finrank_le_of_le hNL hrk' (Submodule.subset_span ⟨j, rfl⟩)
  have key : ∀ x ∈ Submodule.span ℤ (Set.range fun k => τ (s k)), x y y = 0 := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact (hP (s k)).2 ⟨k, rfl⟩ y hy
    | zero => simp
    | add x z _ _ h1 h2 => simp [h1, h2]
    | smul a x _ h => simp [h]
  have h3 := key _ hnmem
  simp only [LinearMap.smul_apply, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3).resolve_left hn

end GlobalTheory.PolFan.Mark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentreDepthLeStarDepthOfCell
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

theorem depth_le_starDepth : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (v : LinearMap.BilinForm ℤ X) (t : ℝ), IsCell bar ψ γ → B ∈ rcone γ → v ∈ balForms bar X → (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v ≠ 0 → (∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v) → 0 ≤ t → B - t • toReal v ∈ rcone γ → t ≤ evalR (starDepth bar ψ w) B := by
  intro O _ bar ψ w X _ _ _ m γ B v t hγ hB hv hvp hvw hvc hv0 huniq ht hBt
  rcases ht.eq_or_lt with rfl | ht
  · exact starDepth_eval_nonneg _
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' O X
  show t ≤ (starDepth bar ψ w).eval X (fun a b => B a b)
  rw [InvFun.eval_eq _ hπ]
  exact le_csSup (_root_.GlobalTheory.PolFan.depthSet_bddAbove_of_unique_centre O bar ψ w X m γ B v hγ hB hv hvp hv0 huniq n π hπ)
    (_root_.GlobalTheory.PolFan.mem_depthSet_of_rcone O bar ψ w X m γ B v t hγ hB hv hvp hvw hvc ht hBt n π hπ)

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisationStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characters_restrict_linear_to_trait_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), IsCN R → P.TorsionIso →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (g : R →+* W) (hg : Function.Injective g), ¬ IsLocalHom g →
    ∀ (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap g)) (P' : PELUnif (maximalIdeal W) t'),
      ∃ ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X, Function.Surjective ρ ∧
        ∀ (a b : P.D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing W)ˣ),
          GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P.D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P'.D.toPre (ρ a) (ρ b) x' →
          ∃ u : Wˣ, IsFractionRing.lift (A := R) (K := FractionRing R)
              (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg) (x : FractionRing R) =
            algebraMap W (FractionRing W) (u : W) * (x' : FractionRing W) := by
  first | exact @GlobalTheory.TauForm.main | exact GlobalTheory.TauForm.main | (intros; apply GlobalTheory.TauForm.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjMulTransposeInv
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.PointChern

open GlobalTheory.HermFrame Matrix

section LinearModel

variable {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ)

noncomputable def linMatEntry (a : Fin p) (b : Fin q) : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => Z u a b
      map_add' := fun u v => by simp
      map_smul' := fun c u => by simp }

theorem mContDiffAt_linMat (k : WithTop ℕ∞) (x : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt k (fun u => Z u) x := fun a b => by
  have : (fun u => Z u a b) = ((linMatEntry Z a b).restrictScalars ℝ : ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ℂ) := by
    funext u; rfl
  rw [this]
  exact ContinuousLinearMap.contDiff _ |>.contDiffAt

theorem mdel_linMat (x ξ : ReciprocityTheory.L2DbarEstimates.V n) : mdel (fun u => Z u) x ξ = Z ξ := by
  ext a b
  have : (fun u => Z u a b) = fun u => linMatEntry Z a b u := rfl
  rw [mdel_apply, this, del_eq_fderiv (linMatEntry Z a b).differentiableAt,
    ContinuousLinearMap.fderiv]
  rfl

theorem mdbar_linMat (x η : ReciprocityTheory.L2DbarEstimates.V n) : mdbar (fun u => Z u) x η = 0 := by
  ext a b
  have : (fun u => Z u a b) = fun u => linMatEntry Z a b u := rfl
  rw [mdbar_apply, this, dbar_eq_zero (linMatEntry Z a b).differentiableAt]
  rfl

theorem mdel_linMat_conjTranspose (x ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => (Z u)ᴴ) x ξ = 0 := by
  rw [mdel_conjTranspose, mdbar_linMat, conjTranspose_zero]

theorem mdbar_linMat_conjTranspose (x η : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u => (Z u)ᴴ) x η = (Z η)ᴴ := by
  rw [mdbar_conjTranspose, mdel_linMat]

theorem mdel_const_sub {m l : Type*} {B : ReciprocityTheory.L2DbarEstimates.V n → Matrix m l ℂ}
    {x : ReciprocityTheory.L2DbarEstimates.V n} (C : Matrix m l ℂ) (h : MContDiffAt 1 B x) (ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => C - B u) x ξ = -mdel B x ξ := by
  ext a b
  simp only [mdel_apply, Matrix.sub_apply, Matrix.neg_apply]
  rw [del_sub (differentiableAt_const _) (h.diff a b)]
  simp

theorem mdbar_const_sub {m l : Type*} {B : ReciprocityTheory.L2DbarEstimates.V n → Matrix m l ℂ}
    {x : ReciprocityTheory.L2DbarEstimates.V n} (C : Matrix m l ℂ) (h : MContDiffAt 1 B x) (η : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u => C - B u) x η = -mdbar B x η := by
  ext a b
  simp only [mdbar_apply, Matrix.sub_apply, Matrix.neg_apply]
  rw [dbar_sub (differentiableAt_const _) (h.diff a b)]
  simp

theorem curv_modelGram_lie (w ξ η : ReciprocityTheory.L2DbarEstimates.V n) (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w ξ η =
      -(Z ξ * (1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹) := by
  have hZ : ∀ x, MContDiffAt 2 (fun u => Z u) x := mContDiffAt_linMat Z 2
  have hB : ∀ x, MContDiffAt 2 (fun u => Z u * (Z u)ᴴ) x :=
    fun x => (hZ x).mul (hZ x).conjTranspose
  have hA : ∀ x, MContDiffAt 2 (fun u => 1 - Z u * (Z u)ᴴ) x :=
    fun x => (mContDiffAt_const 1).sub (hB x)
  have hAu : IsUnit (1 - Z w * (Z w)ᴴ).det := by
    rw [det_one_sub_mul_comm]; exact hw.det_pos.ne'.isUnit
  have hH : (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) =
      fun u => ((1 - Z u * (Z u)ᴴ)⁻¹)ᵀ := by
    funext u
    have e : 1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ = (1 - Z u * (Z u)ᴴ)ᵀ := by
      ext a b
      simp [Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, eq_comm, mul_comm]
    rw [e, transpose_nonsing_inv]
  have hconn : ∀ x, IsUnit (1 - Z x * (Z x)ᴴ).det →
      conn (fun u => ((1 - Z u * (Z u)ᴴ)⁻¹)ᵀ) x ξ = Z ξ * (Z x)ᴴ * (1 - Z x * (Z x)ᴴ)⁻¹ := by
    intro x hx
    have h1 : MContDiffAt 1 (fun u => 1 - Z u * (Z u)ᴴ) x := (hA x).of_le one_le_two
    have hZ1 : MContDiffAt 1 (fun u => Z u) x := (hZ x).of_le one_le_two
    have hdA : mdel (fun u => 1 - Z u * (Z u)ᴴ) x ξ = -(Z ξ * (Z x)ᴴ) := by
      rw [mdel_const_sub _ ((hB x).of_le one_le_two), mdel_mul hZ1 hZ1.conjTranspose,
        mdel_linMat, mdel_linMat_conjTranspose, Matrix.mul_zero, zero_add]
    rw [conn, transpose_transpose, nonsing_inv_nonsing_inv _ hx,
      mdel_transpose (fun u => (1 - Z u * (Z u)ᴴ)⁻¹), transpose_transpose, mdel_inv h1 hx, hdA]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc,
      mul_nonsing_inv_cancel_left _ _ hx]
  have hev : (fun x => conn (fun u => ((1 - Z u * (Z u)ᴴ)⁻¹)ᵀ) x ξ) =ᶠ[𝓝 w]
      fun x => Z ξ * (Z x)ᴴ * (1 - Z x * (Z x)ᴴ)⁻¹ :=
    ((hA w).eventually_isUnit hAu).mono fun x hx => hconn x hx
  have h1 : MContDiffAt 1 (fun u => 1 - Z u * (Z u)ᴴ) w := (hA w).of_le one_le_two
  have hZ1 : MContDiffAt 1 (fun u => Z u) w := (hZ w).of_le one_le_two
  have hdA : mdbar (fun u => 1 - Z u * (Z u)ᴴ) w η = -(Z w * (Z η)ᴴ) := by
    rw [mdbar_const_sub _ ((hB w).of_le one_le_two), mdbar_mul hZ1 hZ1.conjTranspose,
      mdbar_linMat, mdbar_linMat_conjTranspose, Matrix.zero_mul, add_zero]
  rw [hH, curv, mdbar_congr hev,
    mdbar_mul ((mContDiffAt_const (Z ξ)).mul hZ1.conjTranspose) (h1.inv hAu), mdbar_inv h1 hAu,
    mdbar_mul (mContDiffAt_const _) hZ1.conjTranspose, mdbar_linMat_conjTranspose, mdbar_const,
    hdA]
  have hP : (1 - Z w * (Z w)ᴴ) * (1 - Z w * (Z w)ᴴ)⁻¹ = 1 := mul_nonsing_inv _ hAu
  have hQ : (1 - (Z w)ᴴ * Z w)⁻¹ = 1 + (Z w)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z w := by
    apply Matrix.inv_eq_right_inv
    have e : (1 - (Z w)ᴴ * Z w) * (1 + (Z w)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z w) =
        1 - (Z w)ᴴ * Z w + (Z w)ᴴ * ((1 - Z w * (Z w)ᴴ) * (1 - Z w * (Z w)ᴴ)⁻¹) * Z w := by
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
    rw [e, hP, Matrix.mul_one, sub_add_cancel]
  rw [hQ]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, neg_neg, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_assoc, neg_add]
  abel

end LinearModel

end GlobalTheory.PointChern
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjugateEmbedding
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.PointChern

open GlobalTheory.HermFrame Matrix

section ModelCurv

variable {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ)

def entryCLM (a : Fin p) (b : Fin q) : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℂ ℂ a b) ∘ₗ Z)

theorem mContDiffAt_linear {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt k (fun u => Z u) x := fun a b => by
  have : (fun u => Z u a b) = ⇑(entryCLM Z a b) := rfl
  rw [this]
  exact ((entryCLM Z a b).contDiff.restrict_scalars ℝ).contDiffAt

theorem mdel_linear (x ξ : ReciprocityTheory.L2DbarEstimates.V n) : mdel (fun u => Z u) x ξ = Z ξ := by
  ext a b
  rw [mdel_apply]
  have : (fun u => Z u a b) = ⇑(entryCLM Z a b) := rfl
  rw [this, del_eq_fderiv (entryCLM Z a b).differentiableAt, (entryCLM Z a b).fderiv]
  rfl

theorem mdbar_linear (x η : ReciprocityTheory.L2DbarEstimates.V n) : mdbar (fun u => Z u) x η = 0 := by
  ext a b
  rw [mdbar_apply]
  have : (fun u => Z u a b) = ⇑(entryCLM Z a b) := rfl
  rw [this, dbar_eq_zero (entryCLM Z a b).differentiableAt]
  rfl

theorem mdel_one_sub_gram (x ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => 1 - (Z u)ᴴ * Z u) x ξ = -((Z x)ᴴ * Z ξ) := by
  have h1 : MContDiffAt 1 (fun u => Z u) x := mContDiffAt_linear Z x
  have h := mdel_mul (A := fun u => (Z u)ᴴ) h1.conjTranspose h1 ξ
  rw [mdel_linear, mdel_conjTranspose, mdbar_linear, conjTranspose_zero, Matrix.zero_mul,
    add_zero] at h
  have e : (fun u => 1 - (Z u)ᴴ * Z u) = fun u => (fun _ => (1 : Matrix (Fin q) (Fin q) ℂ)) u
      + (fun u => -((Z u)ᴴ * Z u)) u := by funext u; simp [sub_eq_add_neg]
  rw [e, mdel_add (mContDiffAt_const _) (h1.conjTranspose.mul h1).neg, mdel_const, zero_add,
    mdel_neg, h]

theorem mdbar_one_sub_gram (x η : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u => 1 - (Z u)ᴴ * Z u) x η = -((Z η)ᴴ * Z x) := by
  have h1 : MContDiffAt 1 (fun u => Z u) x := mContDiffAt_linear Z x
  have h := mdbar_mul (A := fun u => (Z u)ᴴ) h1.conjTranspose h1 η
  rw [mdbar_linear, mdbar_conjTranspose, mdel_linear, Matrix.mul_zero, zero_add] at h
  have e : (fun u => 1 - (Z u)ᴴ * Z u) = fun u => (fun _ => (1 : Matrix (Fin q) (Fin q) ℂ)) u
      + (fun u => -((Z u)ᴴ * Z u)) u := by funext u; simp [sub_eq_add_neg]
  rw [e, mdbar_add (mContDiffAt_const _) (h1.conjTranspose.mul h1).neg, mdbar_const, zero_add,
    mdbar_neg, h]

theorem inv_one_sub_mul_conjTranspose (z : Matrix (Fin p) (Fin q) ℂ) (hu : IsUnit (1 - zᴴ * z).det) :
    (1 - z * zᴴ)⁻¹ = 1 + z * (1 - zᴴ * z)⁻¹ * zᴴ := by
  apply Matrix.inv_eq_right_inv
  have hAQ : (1 - zᴴ * z) * (1 - zᴴ * z)⁻¹ = 1 := mul_nonsing_inv _ hu
  set Q := (1 - zᴴ * z)⁻¹
  have hQ : Q = 1 + zᴴ * (z * Q) := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add] at hAQ
    rw [Matrix.mul_assoc] at hAQ
    exact hAQ
  have key : z * (Q * zᴴ) = z * zᴴ + z * (zᴴ * (z * (Q * zᴴ))) := by
    nth_rewrite 1 [hQ]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_assoc]
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  nth_rewrite 1 [key]
  abel

theorem curv_inv_one_sub_gram (w ξ η : ReciprocityTheory.L2DbarEstimates.V n) (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η =
      -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ := by
  have hA : ∀ x, MContDiffAt 2 (fun u => 1 - (Z u)ᴴ * Z u) x := fun x =>
    (mContDiffAt_const 1).sub ((mContDiffAt_linear Z x).conjTranspose.mul (mContDiffAt_linear Z x))
  have hu : IsUnit (1 - (Z w)ᴴ * Z w).det := hw.det_pos.ne'.isUnit
  have hconn : ∀ x, IsUnit (1 - (Z x)ᴴ * Z x).det →
      conn (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) x ξ = ((1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ)ᵀ := by
    intro x hx
    have h : (((1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ)ᵀ)ᵀ * (1 - (Z x)ᴴ * Z x)⁻¹ =
        mdel (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) x ξ := by
      rw [transpose_transpose, mdel_inv ((hA x).of_le one_le_two) hx, mdel_one_sub_gram]
      simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    exact (eq_conn_of_compatible (H := fun u => (1 - (Z u)ᴴ * Z u)⁻¹) (z := x)
      (isUnit_nonsing_inv_det _ hx) h).symm
  have he : (fun x => conn (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) x ξ) =ᶠ[𝓝 w]
      fun x => ((1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ)ᵀ :=
    ((hA w).eventually_isUnit hu).mono fun x hx => hconn x hx
  have hI : MContDiffAt 1 (fun x => (1 - (Z x)ᴴ * Z x)⁻¹) w := ((hA w).of_le one_le_two).inv hu
  have h1 : MContDiffAt 1 (fun u => Z u) w := mContDiffAt_linear Z w
  rw [curv, mdbar_congr he, mdbar_transpose (fun x => (1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ),
    mdbar_mul (A := fun x => (1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ) (B := fun _ => Z ξ)
      (hI.mul h1.conjTranspose) (mContDiffAt_const (Z ξ)), mdbar_const, Matrix.mul_zero, zero_add,
    mdbar_mul (A := fun x => (1 - (Z x)ᴴ * Z x)⁻¹) (B := fun x => (Z x)ᴴ) hI h1.conjTranspose,
    mdbar_inv ((hA w).of_le one_le_two) hu, mdbar_one_sub_gram, mdbar_conjTranspose, mdel_linear,
    inv_one_sub_mul_conjTranspose (Z w) hu]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
    neg_neg, Matrix.mul_assoc]

end ModelCurv

theorem curv_modelGram_tauBar : ∀ {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ)
    (w ξ η : ReciprocityTheory.L2DbarEstimates.V n), (1 - (Z w)ᴴ * Z w).PosDef →
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η =
      -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ :=
  fun Z w ξ η hw => curv_inv_one_sub_gram Z w ξ η hw

end GlobalTheory.PointChern
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffReindexFrame
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.ChernReindex

variable {n a b : ℕ}

theorem mdel_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.mdel (fun u => Matrix.reindex e e (H u)) z ξ = Matrix.reindex e e (GlobalTheory.HermFrame.mdel H z ξ) := by
  ext i j; rfl

theorem conn_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.conn (fun u => Matrix.reindex e e (H u)) z ξ = Matrix.reindex e e (GlobalTheory.HermFrame.conn H z ξ) := by
  rw [GlobalTheory.HermFrame.conn, GlobalTheory.HermFrame.conn, mdel_reindex, Matrix.transpose_reindex, Matrix.transpose_reindex,
    Matrix.inv_reindex, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]

theorem curv_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ η : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.curv (fun u => Matrix.reindex e e (H u)) z ξ η = Matrix.reindex e e (GlobalTheory.HermFrame.curv H z ξ η) := by
  unfold GlobalTheory.HermFrame.curv
  simp_rw [conn_reindex]
  ext i j; rfl

theorem curvPoly_reindex (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.GoodMetric.curvPoly (fun u => Matrix.reindex e e (F u)) v = Matrix.reindex e e (GlobalTheory.GoodMetric.curvPoly F v) := by
  refine Matrix.ext fun i j => ?_
  simp only [GlobalTheory.GoodMetric.curvPoly, curv_reindex]
  rfl

theorem charpolyRev_reindex {R : Type} [CommRing R] (e : Fin a ≃ Fin b) (M : Matrix (Fin a) (Fin a) R) :
    (Matrix.reindex e e M).charpolyRev = M.charpolyRev := by
  rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly, Matrix.charpoly_reindex]

theorem chernPoly_reindex : ∀ {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ), chernPoly (fun u => Matrix.reindex e e (F u)) v k = chernPoly F v k := by
  intro n a b e F v k
  rw [GlobalTheory.GoodMetric.chernPoly, GlobalTheory.GoodMetric.chernPoly, curvPoly_reindex,
    show -(Matrix.reindex e e (GlobalTheory.GoodMetric.curvPoly F v)) = Matrix.reindex e e (-GlobalTheory.GoodMetric.curvPoly F v) from by
      ext i j; rfl, charpolyRev_reindex]

end GlobalTheory.ChernReindex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityEqZeroOfWeightedDegreeNeDimStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPolyTopDensity_eq_zero_of_weightedDegree_ne_dim : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (Q : MvPolynomial (ι × ℕ) ℝ) (d : ℕ), MvPolynomial.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) Q d → d ≠ n → chernTop Q G v = 0 := by
  first | exact @GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous | exact GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous | (intros; apply GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous <;> assumption)
end

