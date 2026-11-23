module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsLogGrNormSubLe
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.HTFrame

attribute [local instance] Over.cartesianMonoidalCategory

theorem abs_log_sInf_sub_le {A B : Set ℝ} {c : ℝ} (hc : 1 ≤ c) (hB : ∀ r ∈ B, 0 ≤ r) (hAB : A ⊆ B)
    (hBA : ∀ r ∈ B, c * r ∈ A) : |Real.log (sInf A) - Real.log (sInf B)| ≤ Real.log c := by
  have hc0 : 0 < c := by linarith
  rcases B.eq_empty_or_nonempty with rfl | hne
  · rw [Set.subset_empty_iff.1 hAB, sub_self, abs_zero]
    exact Real.log_nonneg hc
  obtain ⟨r0, hr0⟩ := hne
  have bB : BddBelow B := ⟨0, hB⟩
  have bA : BddBelow A := bB.mono hAB
  have h1 : sInf B ≤ sInf A := csInf_le_csInf bB ⟨_, hBA r0 hr0⟩ hAB
  have h2 : sInf A ≤ c * sInf B := by
    rw [← div_le_iff₀' hc0]
    exact le_csInf ⟨r0, hr0⟩ fun r hr => (div_le_iff₀' hc0).2 (csInf_le bA (hBA r hr))
  have h0 : 0 ≤ sInf B := le_csInf ⟨r0, hr0⟩ hB
  rcases h0.eq_or_lt with h | h
  · have : sInf A = sInf B := le_antisymm (by rw [← h] at h2 ⊢; simpa using h2) h1
    rw [this, sub_self, abs_zero]
    exact Real.log_nonneg hc
  · have h3 := Real.log_le_log h h1
    have h4 := Real.log_le_log (h.trans_le h1) h2
    rw [Real.log_mul hc0.ne' h.ne'] at h4
    rw [abs_of_nonneg (by linarith)]
    linarith

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)


open MonObj in
theorem comb_smul {S : Type} [CommRing S] (a : S) {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) : IsCombAtG t x v (fun i => a * cf i) (spMap (epsMul a) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG x ⟶ tEpsG x := Over.homMk (spMap (epsMul a)) (by
    show spMap (epsMul a) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S (DualNumber S)) ≫ x
    rw [← Category.assoc, spMap_comp']
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, spMap_comp']
    congr 2
    refine RingHom.ext fun r => ?_
    ext
    · simp [epsMul]
    · simp [epsMul]
      ring
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

theorem abs_log_grNorm_sub_le (x : Sp C ⟶ X) {Λ Λ' : Set (Sp (DualNumber C) ⟶ t.G.left)} {a : C} (ha : a ≠ 0)
    (ha1 : ‖a‖ ≤ 1) (h1 : Λ ⊆ Λ') (h2 : ∀ v ∈ Λ', spMap (epsMul a) ≫ v ∈ Λ) {m : ℕ}
    (u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)) (i : Fin m) :
    |Real.log (grNorm t x Λ u i) - Real.log (grNorm t x Λ' u i)| ≤ Real.log ‖a‖⁻¹ := by
  refine abs_log_sInf_sub_le ((one_le_inv₀ (norm_pos_iff.2 ha)).2 ha1) ?_ ?_ ?_
  · rintro r ⟨cf, -, -, -, rfl⟩
    positivity
  · rintro r ⟨cf, h3, h4, ⟨w, hw, hc⟩, rfl⟩
    exact ⟨cf, h3, h4, ⟨w, h1 hw, hc⟩, rfl⟩
  · rintro r ⟨cf, h3, h4, ⟨w, hw, hc⟩, rfl⟩
    refine ⟨fun k => a * cf k, mul_ne_zero ha h3, fun k hk => by simp [h4 k hk], ⟨_, h2 w hw, comb_smul t a hc⟩, ?_⟩
    rw [norm_mul, mul_inv]

end Lat

section Ext

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Ext

end GlobalTheory.HTFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedCombinationOfSpanCoordinateRows
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.combo_of_bounded_rows_bounded : ∀ (X : Type) (g r r₀ : ℕ) (T : Set X) (lam : X → Fin r → Fin g → ℂ) (u : X → Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ) (C : ℝ), (∀ x ∈ T, ∀ i, u x i = ∑ m, A i m • lam x m) → (∀ x ∈ T, ‖u x‖ ≤ C) → ∀ w ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)), ∃ C' : ℝ, ∀ x ∈ T, ‖∑ j, (w j : ℂ) • lam x j‖ ≤ C' := by
  intro X g r r₀ T lam u A C hu hC w hw
  rw [Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨c, rfl⟩ := hw
  refine ⟨∑ i, |c i| * C, fun x hx => ?_⟩
  have key : ∑ j, ((∑ i, c i • fun j => (A i j : ℝ)) j : ℂ) • lam x j = ∑ i, (c i : ℂ) • u x i := by
    simp_rw [hu x hx, Finset.smul_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul, Int.cast_smul_eq_zsmul]
  rw [key]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (u x) i).trans (hC x hx)) (abs_nonneg _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFlagBaseHolds
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Cht.FlagBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem comp_listProd {B : Scheme.{0}} {G : Over B} [GrpObj G] {X Y : Over B} (e : X ⟶ Y) (L : List (Y ⟶ G)) :
    e ≫ L.prod = (L.map (e ≫ ·)).prod := by
  induction L with
  | nil => exact MonObj.comp_one e
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

theorem isCombAtG_bc {X : Scheme.{0}} (t : SAB H X) {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')
    {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) :
    IsCombAtG t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ v j) (fun j => ψ (a j)) (spMap (dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, hw⟩ := h
  have he : spMap (dualMap ψ) ≫ (tEpsG x).hom = (tEpsG (spMap ψ ≫ x)).hom := by
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let e : tEpsG (spMap ψ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap ψ)) he
  refine ⟨fun i => e ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap ψ) ≫ (u i).left = spMap (epsMul (ψ (a i))) ≫ spMap (dualMap ψ) ≫ v i
    rw [hu i, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, epsMul, _root_.mul_comm]
  · have hl : (List.ofFn fun i => e ≫ u i) = (List.ofFn u).map (e ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [hl, ← comp_listProd, Over.comp_left, hw]
    rfl

end GlobalTheory.LocM.Cht.FlagBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoisotropicSublatticeOfTorsionCount
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoisoCount

open Matrix

theorem vecMul_eq_zero_of_rows_li {K : Type*} [Field K] {m n : Type*} [Fintype m]
    (X : Matrix m n K) (h : LinearIndependent K (fun i => X i)) (y : m → K)
    (hy : y ᵥ* X = 0) : y = 0 := by
  rw [Fintype.linearIndependent_iff] at h
  funext i; exact h y (by rw [← vecMul_eq_sum]; exact hy) i

theorem rows_li_of_vecMul {K : Type*} [Field K] {m n : Type*} [Fintype m]
    (X : Matrix m n K) (h : ∀ y : m → K, y ᵥ* X = 0 → y = 0) :
    LinearIndependent K (fun i => X i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [h g (by rw [vecMul_eq_sum]; exact hg)]; rfl

theorem det_gram_ne_zero {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] (X : Matrix m n K)
    (h : ∀ y : m → K, y ᵥ* X = 0 → y = 0) : (X * Xᵀ).det ≠ 0 := by
  intro hd
  obtain ⟨y, hy0, hy⟩ := (Matrix.exists_vecMul_eq_zero_iff).2 hd
  apply hy0; apply h
  apply dotProduct_self_eq_zero.1
  have : (y ᵥ* X) ⬝ᵥ (y ᵥ* X) = y ⬝ᵥ (X *ᵥ (y ᵥ* X)) := by rw [dotProduct_mulVec]
  rw [this, ← vecMul_transpose, vecMul_vecMul, hy, dotProduct_zero]

theorem gram_map {K : Type*} [CommRing K] {m n : Type*} [Fintype n] (Z : Matrix m n ℤ) :
    Z.map (Int.cast : ℤ → K) * (Z.map (Int.cast : ℤ → K))ᵀ = (Z * Zᵀ).map (Int.cast : ℤ → K) := by
  ext i j; simp [Matrix.mul_apply]

theorem det_map_intCast {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]
    (Z : Matrix n n ℤ) : (Z.map (Int.cast : ℤ → K)).det = (Z.det : K) := by
  have := RingHom.map_det (Int.castRingHom K) Z
  simpa using this.symm

theorem rank_bound {r r₀ : ℕ} (P : Matrix (Fin r₀) (Fin r₀) ℤ)
    (hS : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ r ∧
      ∀ x ∈ S, P.map (Int.cast : ℤ → ZMod N) *ᵥ x = 0) :
    r + (P.map (Int.cast : ℤ → ℝ)).rank ≤ 2 * r₀ := by
  classical
  set Pr := P.map (Int.cast : ℤ → ℝ) with hPr
  obtain ⟨κ, c, hc, hsp, hli⟩ := exists_linearIndependent' ℝ (fun k => Pr k)
  haveI : Finite κ := Finite.of_injective c hc
  letI : Fintype κ := Fintype.ofFinite κ
  have hρ : Pr.rank = Nat.card κ := by
    rw [Matrix.rank_eq_finrank_span_row, Nat.card_eq_fintype_card, ← finrank_span_eq_card hli, hsp]; rfl
  set R : Matrix κ (Fin r₀) ℤ := P.submatrix c id with hR
  have hRr : ∀ y : κ → ℝ, y ᵥ* R.map (Int.cast : ℤ → ℝ) = 0 → y = 0 :=
    vecMul_eq_zero_of_rows_li _ hli
  have hd0 : (R * Rᵀ).det ≠ 0 := by
    intro h0
    apply det_gram_ne_zero _ hRr
    rw [gram_map, det_map_intCast, h0, Int.cast_zero]
  set d := (R * Rᵀ).det
  set N := d.natAbs + 1 with hN
  have hN2 : 2 ≤ N := by have := Int.natAbs_pos.2 hd0; omega
  haveI : NeZero N := ⟨by omega⟩
  have hu : IsUnit (d : ZMod N) := by
    have h1 : ((d.natAbs : ℕ) : ZMod N) = -1 := by
      have : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
      rw [hN] at this; push_cast at this; exact eq_neg_of_add_eq_zero_left this
    rcases Int.natAbs_eq d with h | h
    · rw [h, Int.cast_natCast, h1]; exact isUnit_one.neg
    · rw [h, Int.cast_neg, Int.cast_natCast, h1, neg_neg]; exact isUnit_one
  obtain ⟨S, hcard, hSk⟩ := hS N (by omega)
  set RN := R.map (Int.cast : ℤ → ZMod N) with hRN
  let f : (Fin r₀ → ZMod N) →+ (κ → ZMod N) := RN.mulVecLin.toAddMonoidHom
  have hsurj : Function.Surjective f := by
    intro z
    have hG : IsUnit (RN * RNᵀ).det := by rw [hRN, gram_map, det_map_intCast]; exact hu
    refine ⟨RNᵀ *ᵥ ((RN * RNᵀ)⁻¹ *ᵥ z), ?_⟩
    show RN *ᵥ (RNᵀ *ᵥ _) = z
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, one_mulVec]
  have hkc : Nat.card f.ker * N ^ Nat.card κ = N ^ r₀ := by
    have h1 := f.ker.card_mul_index
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top,
      Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin r₀),
      Fintype.card_fin] at h1
    exact h1
  have hsub : S ⊆ (f.ker : Set (Fin r₀ → ZMod N)) := by
    intro x hx
    show RN *ᵥ x = 0
    funext k
    have := congrFun (hSk x hx) (c k)
    exact this
  have hle : Nat.card S ≤ Nat.card f.ker := Nat.card_mono (Set.toFinite _) hsub
  have key : N ^ r * N ^ Nat.card κ ≤ N ^ r₀ * N ^ r₀ := by
    rw [← hcard, ← hkc, _root_.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hle)
  rw [← pow_add, ← pow_add] at key
  have := (Nat.pow_le_pow_iff_right hN2).1 key
  rw [hρ]; omega

end GlobalTheory.CoisoCount

namespace GlobalTheory.CoisoCount

open Matrix

theorem ker_le_span {r r₀ : ℕ} (Mr : Matrix (Fin r) (Fin r) ℝ) (Ar : Matrix (Fin r₀) (Fin r) ℝ)
    (hM : IsUnit Mr.det) (hA : LinearIndependent ℝ (fun i => Ar i))
    (hρ : r + (Ar * Mrᵀ * Arᵀ).rank ≤ 2 * r₀) :
    LinearMap.ker (Ar * Mrᵀ).mulVecLin ≤ Submodule.span ℝ (Set.range fun i => Ar i) := by
  set T := (Ar * Mrᵀ).mulVecLin
  set E := Arᵀ.mulVecLin
  have hE : Function.Injective E := by
    intro x y hxy
    have : (x - y) ᵥ* Ar = 0 := by
      rw [sub_vecMul, ← mulVec_transpose, ← mulVec_transpose]; exact sub_eq_zero.2 hxy
    exact sub_eq_zero.1 (vecMul_eq_zero_of_rows_li _ hA _ this)
  have hrE : LinearMap.range E = Submodule.span ℝ (Set.range fun i => Ar i) := by
    rw [Matrix.range_mulVecLin]; rfl
  have hAr : Ar.rank = r₀ := by
    rw [Matrix.rank_eq_finrank_span_row]
    change Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => Ar i)) = r₀
    rw [finrank_span_eq_card hA, Fintype.card_fin]
  have hT : Module.finrank ℝ (LinearMap.range T) = r₀ := by
    change (Ar * Mrᵀ).rank = r₀
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by rwa [Matrix.det_transpose]), hAr]
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 := LinearMap.finrank_range_add_finrank_ker (T ∘ₗ E)
  have hQ : Module.finrank ℝ (LinearMap.range (T ∘ₗ E)) = (Ar * Mrᵀ * Arᵀ).rank := by
    rw [Matrix.rank, Matrix.mulVecLin_mul]
  have hmap : Submodule.map E (LinearMap.ker (T ∘ₗ E)) = LinearMap.range E ⊓ LinearMap.ker T := by
    rw [LinearMap.ker_comp, Submodule.map_comap_eq]
  have h3 : Module.finrank ℝ (LinearMap.range E ⊓ LinearMap.ker T : Submodule ℝ (Fin r → ℝ)) =
      Module.finrank ℝ (LinearMap.ker (T ∘ₗ E)) := by
    rw [← hmap]; exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective E hE _)).symm
  rw [Module.finrank_fin_fun] at h1 h2
  have heq := Submodule.eq_of_le_of_finrank_le
    (inf_le_right : LinearMap.range E ⊓ LinearMap.ker T ≤ LinearMap.ker T) (by omega)
  rw [← hrE, ← heq]; exact inf_le_left

theorem gramQ {r r₀ : ℕ} (M : Matrix (Fin r) (Fin r) ℤ) (A : Fin r₀ → Fin r → ℤ) :
    (Matrix.of fun i j => (A i j : ℝ)) * (M.map (Int.cast : ℤ → ℝ))ᵀ * (Matrix.of fun i j => (A i j : ℝ))ᵀ
      = (Matrix.of fun k i => A i ⬝ᵥ M *ᵥ A k).map (Int.cast : ℤ → ℝ) := by
  ext i k
  simp [Matrix.mul_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.CoisoCount

namespace GlobalTheory.CoisoCount

open Matrix

theorem coisotropic_of_torsion_count (r r₀ : ℕ) (M : Matrix (Fin r) (Fin r) ℤ)
    (A : Fin r₀ → Fin r → ℤ) (hM : M.det ≠ 0)
    (hA : LinearIndependent ℚ (fun i j => (A i j : ℚ)))
    (hS : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ r ∧
      ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S →
        (N : ℤ) ∣ (∑ i, a i • A i) ⬝ᵥ M *ᵥ (∑ i, a' i • A i))
    (v : Fin r → ℝ)
    (hv : ∀ i, v ⬝ᵥ (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (A i j : ℝ)) = 0) :
    v ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)) := by
  classical
  set Ar : Matrix (Fin r₀) (Fin r) ℝ := Matrix.of fun i j => (A i j : ℝ) with hAr
  set Mr := M.map (Int.cast : ℤ → ℝ) with hMr
  set P : Matrix (Fin r₀) (Fin r₀) ℤ := Matrix.of fun k i => A i ⬝ᵥ M *ᵥ A k with hP
  have hAz : ((Matrix.of A) * (Matrix.of A)ᵀ).det ≠ 0 := by
    intro h0
    apply det_gram_ne_zero ((Matrix.of A).map (Int.cast : ℤ → ℚ))
      (vecMul_eq_zero_of_rows_li ((Matrix.of A).map (Int.cast : ℤ → ℚ)) hA)
    rw [gram_map, det_map_intCast, h0, Int.cast_zero]
  have hArli : LinearIndependent ℝ (fun i => Ar i) := by
    apply rows_li_of_vecMul
    intro y hy
    have hdet : (Ar * Arᵀ).det ≠ 0 := by
      have : Ar = (Matrix.of A).map (Int.cast : ℤ → ℝ) := rfl
      rw [this, gram_map, det_map_intCast]; exact_mod_cast hAz
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    rw [← vecMul_vecMul, hy, zero_vecMul]
  have hMu : IsUnit Mr.det := by
    rw [hMr, det_map_intCast]; exact isUnit_iff_ne_zero.2 (by exact_mod_cast hM)
  have hρ : r + (Ar * Mrᵀ * Arᵀ).rank ≤ 2 * r₀ := by
    rw [hAr, hMr, gramQ]
    apply rank_bound P
    intro N hN
    haveI : NeZero N := ⟨hN.ne'⟩
    obtain ⟨S, hc, hS'⟩ := hS N hN
    refine ⟨S, hc, fun x hx => ?_⟩
    funext k
    set a : Fin r₀ → ℤ := fun i => ((x i).val : ℤ) with ha_def
    have ha : (fun j => (a j : ZMod N)) = x := by funext j; simp only [a]; rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hdv := hS' a (Pi.single k 1) (by rw [ha]; exact hx)
    have hsum : (∑ i, (Pi.single k (1 : ℤ) : Fin r₀ → ℤ) i • A i) = A k := by
      simp [Pi.single_apply]
    rw [hsum] at hdv
    have hvs : ∑ i, a i • A i = a ᵥ* Matrix.of A := (vecMul_eq_sum _ _).symm
    have hz : (∑ i, a i • A i) ⬝ᵥ M *ᵥ A k = (P *ᵥ a) k := by
      rw [hvs, ← dotProduct_mulVec, dotProduct_comm]; rfl
    rw [hz] at hdv
    have hcast := RingHom.map_mulVec (Int.castRingHom (ZMod N)) P a k
    have e1 : (((P *ᵥ a) k : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdv
    simp only [Int.coe_castRingHom, e1] at hcast
    have h2 : (Int.cast ∘ a : Fin r₀ → ZMod N) = x := ha
    rw [h2] at hcast
    exact hcast.symm
  have hker : v ∈ LinearMap.ker (Ar * Mrᵀ).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    rw [← mulVec_mulVec, mulVec_transpose]
    have := hv i
    rw [dotProduct_mulVec, dotProduct_comm] at this
    exact this
  exact ker_le_span Mr Ar hMu hArli hρ hker

end GlobalTheory.CoisoCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapMulIdealSheaf
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Principalise

theorem comap_mul_idealSheaf : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) (I J : X.IdealSheafData),
    (I * J).comap f = I.comap f * J.comap f := by
  intro X X' f I J
  have h : ∀ y : X', ∃ (U : X.affineOpens) (A : X'.affineOpens), y ∈ A.1 ∧ A.1 ≤ f ⁻¹ᵁ U.1 := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ
    obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAU⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ f ⁻¹ᵁ U from hyU) (f ⁻¹ᵁ U).isOpen
    exact ⟨⟨U, hU⟩, ⟨A, hA⟩, hyA, hAU⟩
  choose U A hyA hAU using h
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top A ?_ fun y => ?_
  · exact top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyA y⟩
  · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, comapIdealAffine _ f (U y) (A y) (hAU y),
      comapIdealAffine _ f (U y) (A y) (hAU y), comapIdealAffine _ f (U y) (A y) (hAU y),
      Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]

end GlobalTheory.Principalise
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCover
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem noetherianSpace_cell {X : Scheme.{0}} [IsLocallyNoetherian X] {T : Type} [Finite T] (m : T → ℕ)
    (U : X.affineOpens) : TopologicalSpace.NoetherianSpace (Sp (CR m U)) := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing (CR m U) := inferInstance
  exact inferInstanceAs (TopologicalSpace.NoetherianSpace (PrimeSpectrum (CR m U)))

theorem compact_normal_noetherian_of_cells : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (F : Scheme.{0}) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ b w, IsOpenImmersion (i b w)) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → CompactSpace F ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme F ∧ TopologicalSpace.NoetherianSpace F := by
  intro X _ T _ m B _ V F i hX hi hc
  have hN : TopologicalSpace.NoetherianSpace F := by
    have h1 : ∀ a : B × Pm m, TopologicalSpace.NoetherianSpace (Set.range (i a.1 a.2)) := fun a => by
      have := noetherianSpace_cell m (V a.1)
      exact TopologicalSpace.NoetherianSpace.range _ (i a.1 a.2).continuous
    have h2 := TopologicalSpace.NoetherianSpace.iUnion (fun a : B × Pm m => Set.range (i a.1 a.2))
    have h3 : (⋃ a : B × Pm m, Set.range (i a.1 a.2)) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨b, w, h⟩ := hc x
      exact Set.mem_iUnion.2 ⟨(b, w), h⟩
    rw [h3] at h2
    exact TopologicalSpace.noetherian_univ_iff.1 h2
  refine ⟨inferInstance, fun x => ?_, hN⟩
  obtain ⟨b, w, y, rfl⟩ := hc x
  have := hi b w
  obtain ⟨_, _⟩ := (cell_smooth_normal X T m (V b) hX).2 y
  let e := (asIso ((i b w).stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

end GlobalTheory.FlagEmb
end

