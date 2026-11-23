module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.AutSimilitudeAndMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta
open Matrix

variable {g : ℕ}

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma exists_column_sum_eq_add_two_mul (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (c : Fin 4) :
    ∃ s : ℤ, ∑ r, al r c = m + 2 * s := by
  have h1 : ∑ r, al r c * al r c = m := by
    have := congrFun (congrFun hal c) c
    simpa [Matrix.mul_apply] using this
  have h2 : Even (∑ r, al r c * (al r c - 1)) := Finset.even_sum _ fun r _ => Int.even_mul_pred_self _
  obtain ⟨s, hs⟩ := h2
  refine ⟨-s, ?_⟩
  have : ∑ r, al r c * (al r c - 1) = ∑ r, al r c * al r c - ∑ r, al r c := by
    simp [mul_sub, Finset.sum_sub_distrib]
  linarith

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma exists_int_two_mul_dotProduct_of_half_integral {g : ℕ} (a : Fin g → ℂ) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (k : Fin g → ℤ) :
    ∃ t : ℤ, 2 * (a ⬝ᵥ fun i => (k i : ℂ)) = t := by
  refine ⟨∑ i, if a i = 0 then 0 else k i, ?_⟩
  simp only [dotProduct, Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases ha i with h | h <;> simp [h]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma sum_intCast_mul_column_eq_of_transpose_mul_eq_smul (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (c c' : Fin 4) :
    ∑ r, (al r c : ℂ) * al r c' = if c = c' then (m : ℂ) else 0 := by
  have := congrFun (congrFun hal c) c'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this
  split_ifs at this ⊢ with h <;> [skip; skip] <;> exact_mod_cast (by simpa using this)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma sum_column_smul_add_tors_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (m : ℕ) (hm : 1 ≤ m) (al : Matrix (Fin 4) (Fin 4) ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ) (c : Fin 4) :
    ∑ r, (al r c : ℂ) • (∑ c', al r c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n r) = (m : ℂ) • y c + _root_.GlobalTheory.SimilTheta.lat τ (k c) (n c) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold _root_.GlobalTheory.SimilTheta.tors
  simp only [← Int.cast_smul_eq_zsmul ℂ, smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun r c' => ((al r c : ℂ) * al r c') • y c')]
  simp only [← Finset.sum_smul, sum_intCast_mul_column_eq_of_transpose_mul_eq_smul m al hal]
  have h2 : ∀ x x_1, (↑(al x c) * ((↑m)⁻¹ * ↑(al x x_1)) : ℂ) = (↑m)⁻¹ * (↑(al x c) * ↑(al x x_1)) := fun _ _ => by ring
  have h3 : ∑ x, ∑ x_1, (↑(al x c) * ((↑m)⁻¹ * ↑(al x x_1)) : ℂ) • _root_.GlobalTheory.SimilTheta.lat τ (k x_1) (n x_1) = _root_.GlobalTheory.SimilTheta.lat τ (k c) (n c) := by
    rw [Finset.sum_comm]
    simp only [h2, ← Finset.sum_smul, ← Finset.mul_sum, sum_intCast_mul_column_eq_of_transpose_mul_eq_smul m al hal]
    simp [mul_ite, inv_mul_cancel₀ hm0]
  rw [h3]
  simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma intCast_zsmul_vector {g : ℕ} (α : ℤ) (v : Fin g → ℤ) :
    (fun i => (((α • v) i : ℤ) : ℂ)) = (α : ℂ) • fun i => (v i : ℂ) := by
  ext i; simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
theorem _root_.GlobalTheory.SimilTheta.aut_similitude_and_mul : ∀ (g m : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ), _root_.GlobalTheory.KeyPow.charHalf g a b → τ.IsSymm → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → (∀ (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ) (c : Fin 4) (k₀ n₀ : Fin g → ℤ), (∏ r, _root_.GlobalTheory.SimilTheta.aut τ a b (al r c • k₀) (al r c • n₀) (∑ c', al r c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n r)) * Complex.exp (2 * Real.pi * Complex.I * ((fun i => (n c i : ℂ)) ⬝ᵥ _root_.GlobalTheory.SimilTheta.lat τ k₀ n₀)) = _root_.GlobalTheory.SimilTheta.aut τ a b k₀ n₀ (y c) ^ m) ∧ ∀ (k₀ n₀ : Fin g → ℤ) (z : Fin g → ℂ), _root_.GlobalTheory.SimilTheta.aut τ a b ((m : ℤ) • k₀) ((m : ℤ) • n₀) ((m : ℤ) • z) = _root_.GlobalTheory.SimilTheta.aut τ a b k₀ n₀ z ^ (m ^ 2) := by
  intro g m τ a b al hab hτ hm hal
  refine ⟨fun k n y c k₀ n₀ => ?_, fun k₀ n₀ z => ?_⟩
  · obtain ⟨s, hs⟩ := exists_column_sum_eq_add_two_mul m al hal c
    obtain ⟨ta, hta⟩ := exists_int_two_mul_dotProduct_of_half_integral a hab.1 k₀
    obtain ⟨tb, htb⟩ := exists_int_two_mul_dotProduct_of_half_integral b hab.2 n₀
    have hV := sum_column_smul_add_tors_eq τ m hm al hal k n y c
    unfold _root_.GlobalTheory.SimilTheta.aut
    simp only [intCast_zsmul_vector, smul_dotProduct, dotProduct_smul, mulVec_smul, smul_eq_mul]
    rw [← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
    set K₀ : Fin g → ℂ := fun i => (k₀ i : ℂ)
    set N₀ : Fin g → ℂ := fun i => (n₀ i : ℂ)
    set Kc : Fin g → ℂ := fun i => (k c i : ℂ)
    set Nc : Fin g → ℂ := fun i => (n c i : ℂ)
    have hterm : ∀ x, (2 * ↑Real.pi * Complex.I *
            (((↑(al x c) * a ⬝ᵥ K₀) - ↑(al x c) * b ⬝ᵥ N₀) -
                ↑(al x c) * (↑(al x c) * N₀ ⬝ᵥ τ *ᵥ N₀) / 2 -
              ↑(al x c) * N₀ ⬝ᵥ (∑ c', al x c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n x)) : ℂ) =
        2 * ↑Real.pi * Complex.I * ((al x c : ℂ) * (a ⬝ᵥ K₀ - b ⬝ᵥ N₀) - (al x c : ℂ) * al x c * (N₀ ⬝ᵥ τ *ᵥ N₀ / 2)
          - N₀ ⬝ᵥ ((al x c : ℂ) • (∑ c', al x c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n x))) := by
      intro x
      rw [dotProduct_smul, smul_eq_mul]
      ring
    simp only [hterm]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      ← dotProduct_sum, hV, sum_intCast_mul_column_eq_of_transpose_mul_eq_smul m al hal c c, if_pos rfl]
    have hs' : ∑ x, (al x c : ℂ) = m + 2 * s := by exact_mod_cast hs
    rw [hs']
    have hsym : Nc ⬝ᵥ τ *ᵥ N₀ = N₀ ⬝ᵥ τ *ᵥ Nc := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hτ.eq, dotProduct_comm]
    have hNK : Nc ⬝ᵥ K₀ = ((n c ⬝ᵥ k₀ : ℤ) : ℂ) := by simp [Nc, K₀, dotProduct]
    have hNK' : N₀ ⬝ᵥ Kc = ((n₀ ⬝ᵥ k c : ℤ) : ℂ) := by simp [N₀, Kc, dotProduct]
    unfold _root_.GlobalTheory.SimilTheta.lat
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    refine ⟨s * (ta - tb) + (n c ⬝ᵥ k₀ - n₀ ⬝ᵥ k c), ?_⟩
    push_cast
    rw [← hNK, ← hNK', ← hta, ← htb]
    linear_combination (2 * ↑Real.pi * Complex.I) * hsym
  · obtain ⟨ta, hta⟩ := exists_int_two_mul_dotProduct_of_half_integral a hab.1 k₀
    obtain ⟨tb, htb⟩ := exists_int_two_mul_dotProduct_of_half_integral b hab.2 n₀
    unfold _root_.GlobalTheory.SimilTheta.aut
    simp only [intCast_zsmul_vector, smul_dotProduct, dotProduct_smul, mulVec_smul, smul_eq_mul]
    rw [← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
    obtain ⟨u, hu⟩ := Int.even_mul_pred_self (m : ℤ)
    have hmu : (m : ℂ) * (m - 1) = u + u := by exact_mod_cast hu
    refine ⟨-u * (ta - tb), ?_⟩
    simp only [zsmul_eq_mul, Int.cast_natCast]
    push_cast
    rw [← hta, ← htb]
    linear_combination (-(2 * ↑Real.pi * Complex.I) * ((a ⬝ᵥ fun i ↦ (k₀ i : ℂ)) - b ⬝ᵥ fun i ↦ (n₀ i : ℂ))) * hmu

end GlobalTheory.SimilTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BoxProductsBasisSpanPowObjSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.BoxSpan

variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}

def ev (p : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp
    ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_cst (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (cst p U c) = ev (r ≫ p) z c :=
  (gs_res r z le_top h _).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq _ z ⊤ trivial _))

theorem gs_sum {I : Type} (s : Finset I) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : I → Γ(Y, U)) :
    gs r z U (∑ i ∈ s, a i) = ∑ i ∈ s, gs r z U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq r z U h, map_sum]

theorem exists_sec_pw (L : LB X) (t : ℤ) (a : LB.Sec (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => t))) :
    ∃ a' : LB.Sec (pw L t), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) J, Good L z J →
      sval a r z J = gs r z (L.U (J r)) (a'.f (J r)) := by
  have hle : ∀ i, L.U i ≤ LB.wchart L (K := PUnit) (fun _ => 𝟙 X) (fun _ => i) :=
    fun i _ hy => Set.mem_iInter.2 fun _ => hy
  refine ⟨⟨fun i => rs X (hle i) (a.f fun _ => i), fun i j => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => ?_⟩
  · have hy' : y ∈ L.U i ⊓ L.U j := hy
    refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (hle i) hy'.1 _)).trans
      ((sec_trans a (𝟙 X) y (hle i hy'.1) (hle j hy'.2)).trans (Eq.trans ?_ (gs_mul (𝟙 X) y _ hy _ _).symm))
    refine congrArg₂ (· * ·) ?_ ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (hle j) hy'.2 _)).symm
    refine Eq.trans ?_ (gs_unit (𝟙 X) y (L.U i ⊓ L.U j) hy' (L.g i j ^ t)).symm
    rw [map_zpow]
    exact congrArg Units.val (Fintype.prod_unique (fun _ : PUnit => gm (𝟙 X ≫ 𝟙 X) y (L.U i ⊓ L.U j) (L.g i j) ^ t))
  · rw [sval_of a r z J (fun _ => J r) (fun _ => by rw [Category.comp_id])]
    exact (gs_res r z (hle _) (hJ r) _).symm

theorem isProper_powObj {S : Scheme.{0}} (A : Over S) [GrpObj A] (h : IsAbelianScheme A) :
    ∀ n, IsProper (Out.powObj A n).hom
  | 0 => inferInstanceAs (IsProper (𝟙 S))
  | n + 1 => (AbelianSchemeGerms.isAbelianScheme_powObj A h n).proper

theorem exists_coords (x : KeyIn R) {m N : ℕ} (b : Fin N → RR x m) (hb : IsBasis x b)
    (a : LB.Sec (LB.LinComb x.P.L (K := PUnit) (fun _ => 𝟙 x.P.A.left) (fun _ => (m : ℤ)))) :
    ∃ c : Fin N → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ x.P.A.left) (z : Z) J, Good x.P.L z J →
      sval a r z J = ∑ k, ev (r ≫ x.P.A.hom) z (c k) * gs r z (x.P.L.U (J r)) ((b k).f (J r)) := by
  obtain ⟨a', ha⟩ := exists_sec_pw x.P.L m a
  obtain ⟨c, hc, -⟩ := hb a'
  refine ⟨c, fun Z r z J hJ => (ha Z r z J hJ).trans ((congrArg (gs r z _) (hc (J r))).trans
    ((gs_sum _ r z _ (hJ r) _).trans (Finset.sum_congr rfl fun k _ => ?_)))⟩
  exact (gs_mul r z _ (hJ r) _ _).trans (congrArg (· * _) (gs_cst _ r z _ (hJ r) _))

theorem sum_mul_sum_cons {T : Type} [CommRing T] {E₁ E₂ E : R →+* T} (h₁ : E₁ = E) (h₂ : E₂ = E) {n N k : ℕ}
    (G : Fin (n + 1) → Fin N → T) (c : Fin k → Fin N → R) (q : Fin k → (Fin n → Fin N) → R) :
    ∑ i, (∑ j, E₁ (c i j) * G 0 j) * ∑ I, E₂ (q i I) * ∏ d : Fin n, G d.succ (I d) =
      ∑ I : Fin (n + 1) → Fin N, E (∑ i, c i (I 0) * q i (Fin.tail I)) * ∏ d, G d (I d) := by
  subst h₁ h₂
  rw [← (Fin.consEquiv fun _ => Fin N).sum_comp, Fintype.sum_prod_type]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, map_sum, map_mul]
  simp only [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.tail_cons]
  ring

theorem span_ev (K : Type) [Field K] (x : KeyIn K) (m N : ℕ) (b : Fin N → RR x m) (hb : IsBasis x b) (n : ℕ) :
    ∀ (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))),
      ∃ q : (Fin n → Fin N) → K, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J, Good x.P.L z J →
        sval s r z J = ∑ I, ev (r ≫ (Out.powObj x.P.A n).hom) z (q I) *
          ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left)))
            ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  induction n with
  | zero =>
    intro s
    have hW : LB.wchart x.P.L (K := Fin 0) (fun c => (Out.powPr x.P.A c).left) Fin.elim0 = ⊤ :=
      top_le_iff.1 fun _ _ => Set.mem_iInter.2 fun k => k.elim0
    haveI : IsIso (Out.powObj x.P.A 0).hom := inferInstanceAs (IsIso (𝟙 (Sp K)))
    obtain ⟨c, hc⟩ := (cst_bijective (Out.powObj x.P.A 0).hom hW).2 (s.f Fin.elim0)
    refine ⟨fun _ => c, fun Z r z J hJ => ?_⟩
    rw [sval_of s r z J Fin.elim0 (fun k => k.elim0), ← hc, Fintype.sum_unique, Fin.prod_univ_zero, _root_.mul_one]
    exact gs_cst _ r z _ (Set.mem_iInter.2 fun k => k.elim0) c
  | succ n ih =>
    intro s
    haveI := x.P.isAb.proper
    haveI := isProper_powObj x.P.A x.P.isAb n
    have hF : FormEq (K := Fin (n + 1)) (K' := PUnit ⊕ Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ))
        (Sum.elim (fun _ => (fst x.P.A (Out.powObj x.P.A n)).left ≫ 𝟙 x.P.A.left)
          (fun k => (snd x.P.A (Out.powObj x.P.A n)).left ≫ (Out.powPr x.P.A k).left))
        (Sum.elim (fun _ => (m : ℤ)) (fun _ => (m : ℤ))) := fun U _ h => by
      rw [Fin.prod_univ_succ, Fintype.prod_sum_type]
      exact congrArg₂ (· * ·) (Fintype.prod_unique
        (fun _ : PUnit => h ((fst x.P.A (Out.powObj x.P.A n)).left ≫ 𝟙 x.P.A.left) ^ (m : ℤ))).symm rfl
    obtain ⟨v, hv⟩ := exists_sec x.P.isLB hF s
    obtain ⟨k, a₁, a₂, ha⟩ := (GlobalTheory.T.section_lin_comb_fiber_product_separated K x.P.A.left x.P.L x.P.isLB x.P.A (Out.powObj x.P.A n) PUnit (Fin n)
      (fun _ => 𝟙 x.P.A.left) (fun _ => (m : ℤ)) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ))).1 v
    choose c hc using fun i => exists_coords x b hb (a₁ i)
    choose q hq using fun i => ih (a₂ i)
    refine ⟨fun I => ∑ i, c i (I 0) * q i (Fin.tail I), fun Z r z J hJ => ?_⟩
    refine (hv Z r z J hJ).symm.trans ((ha Z r z J hJ).trans ?_)
    have e₁ : (r ≫ (fst x.P.A (Out.powObj x.P.A n)).left) ≫ x.P.A.hom = r ≫ (Out.powObj x.P.A (n + 1)).hom :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w (fst x.P.A (Out.powObj x.P.A n))))
    have e₂ : (r ≫ (snd x.P.A (Out.powObj x.P.A n)).left) ≫ (Out.powObj x.P.A n).hom =
        r ≫ (Out.powObj x.P.A (n + 1)).hom :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w (snd x.P.A (Out.powObj x.P.A n))))
    refine (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (hc i Z _ z J hJ) (hq i Z _ z J hJ)).trans ?_
    exact sum_mul_sum_cons (congrArg (ev · z) e₁) (congrArg (ev · z) e₂)
      (fun d j => gs (r ≫ (Out.powPr x.P.A d).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A d).left)))
          ((b j).f (J (r ≫ (Out.powPr x.P.A d).left)))) c q

theorem boxProducts_span : ∀ (K : Type) [Field K] (x : KeyIn K) (m N : ℕ) (b : Fin N → RR x m), IsBasis x b → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))), ∃ q : (Fin n → Fin N) → K, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J, Good x.P.L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj x.P.A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  intro K _ x m N b hb n s
  obtain ⟨q, hq⟩ := span_ev K x m N b hb n s
  refine ⟨q, fun Z r z J hJ => (hq Z r z J hJ).trans (Finset.sum_congr rfl fun I _ => ?_)⟩
  rw [gs_cst _ r z ⊤ trivial]

end GlobalTheory.BoxSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BoxProductsSpanExternalPowersOfBoxSpanStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxProducts_span_external_powers_of_boxSpan : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (L : LB A.left) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)), L.IsLB → (∀ T : Over (Sp R), GlobalTheory.RelBasis.BoxSpan b (snd A T).left (fst A T).left) → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb L (K := Fin n) (fun c => (Out.powPr A c).left) (fun _ => t))), ∃ q : (Fin n → Fin N) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj A n).left) (z : Z) J, Good L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr A c).left) z (L.U (J (r ≫ (Out.powPr A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr A c).left))) := by
  first | exact @GlobalTheory.PowSpan.boxProducts_span_of_boxSpan | exact GlobalTheory.PowSpan.boxProducts_span_of_boxSpan | (intros; apply GlobalTheory.PowSpan.boxProducts_span_of_boxSpan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EqOfSimilitudeIsoQuotientKernelInvariantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_similitudeIso_quotient_kernel_invariant : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ ξ' : Fin 4 → Pt x) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (w' : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ' r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → w.IsGen → w'.IsGen → (∀ v : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4, (∀ r, v ≫ alMap x al r 1 = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → val w (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w' r z J = val w' (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w r z J) → ξ = ξ' := by
  first | exact @GlobalTheory.KeyKa.eq_of_similitude_invariant | exact GlobalTheory.KeyKa.eq_of_similitude_invariant | (intros; apply GlobalTheory.KeyKa.eq_of_similitude_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEntireGeneratorDivFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

theorem GlobalTheory.exists_entire_generator_div_frames : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), L.IsLB → ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ A.left)) (ep : K → ℤ) (t : LB.Gen (LB.LinComb L φ ep)), t.IsGen → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (pt : E → (Sp ℂ ⟶ Y)) (z : K → E → Fin g → ℂ), GlobalTheory.PowUnif.IsHolFamily pt → (∀ k, Differentiable ℂ (z k)) → (∀ e k, pt e ≫ φ k = (u.ex (z k e)).left) → ∃ T : E → ℂ, Differentiable ℂ T ∧ (∀ e, T e ≠ 0) ∧ ∀ e (j : K → L.ι), (∀ k, ⊤ ≤ (u.ex (z k e)).left ⁻¹ᵁ L.U (j k)) → valAt' (pt e) (LB.wchart L φ j) (t.s j).val = T e * ∏ k, u.fr (j k) (z k e) ^ ep k := by
  intro A _ L g u hL Y K _ φ ep t ht E _ _ pt z hpt hz hφ
  have hv : GlobalTheory.CubeValues.ValueRules := GlobalTheory.valAt'_rules
  let d : (Fin g → ℂ) → (Sp ℂ ⟶ A.left) := fun w => (u.ex w).left
  have hφ' : ∀ e k, pt e ≫ φ k = d (z k e) := hφ
  have hw : ∀ e (j : K → L.ι), ⊤ ≤ pt e ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ d (z k e) ⁻¹ᵁ L.U (j k) := fun e j => by
    rw [GlobalTheory.PowUnif.le_wchart_iff]
    simp only [hφ']
  choose j₀ hj₀ using fun e k => GlobalTheory.PowUnif.exists_chart hL (d (z k e))
  let ω : (K → L.ι) → E → ℂ := fun j e => valAt' (pt e) (LB.wchart L φ j) (t.s j).val
  let P : (K → L.ι) → E → ℂ := fun j e => ∏ k, u.fr (j k) (z k e) ^ ep k
  have hω : ∀ j e, (∀ k, ⊤ ≤ d (z k e) ⁻¹ᵁ L.U (j k)) → ω j e ≠ 0 := fun j e h =>
    GlobalTheory.valAt'_unit_ne_zero (pt e) ((hw e j).2 h) (t.s j)
  have hP : ∀ j e, (∀ k, ⊤ ≤ d (z k e) ⁻¹ᵁ L.U (j k)) → P j e ≠ 0 := fun j e h =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u.fr_ne _ _ (h k))
  have hG : ∀ j j' e, (∀ k, ⊤ ≤ d (z k e) ⁻¹ᵁ L.U (j k)) → (∀ k, ⊤ ≤ d (z k e) ⁻¹ᵁ L.U (j' k)) →
      ω j e / P j e = ω j' e / P j' e := by
    intro j j' e h h'
    have hk : ∀ k, ⊤ ≤ d (z k e) ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) := fun k =>
      (GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨h k, h' k⟩
    let c : ℂ := ∏ k, valAt' (d (z k e)) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ep k
    have hc : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (GlobalTheory.valAt'_unit_ne_zero _ (hk k) _)
    have e₁ : ω j e = c * ω j' e := by
      refine (GlobalTheory.CubeValues.val_gen (pt e) hv t ht j j' ((hw e j).2 h) ((hw e j').2 h')).trans ?_
      refine congrArg (· * ω j' e) ?_
      refine (GlobalTheory.CubeValues.val_linComb (pt e) hv L φ ep j j' ((hw e j).2 h) ((hw e j').2 h')).trans ?_
      simp only [hφ', c]
    have e₂ : P j e = c * P j' e := by
      simp only [P, c]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← mul_zpow]
      exact congrArg (· ^ ep k) (u.fr_compat _ _ _ (hk k))
    rw [e₁, e₂, mul_div_mul_left _ _ hc]
  refine ⟨fun e => ω (j₀ e) e / P (j₀ e) e, fun e₀ => ?_,
    fun e => div_ne_zero (hω _ _ (hj₀ e)) (hP _ _ (hj₀ e)), fun e j h => ?_⟩
  · have hS := hpt (LB.wchart L φ (j₀ e₀)) (t.s (j₀ e₀)).val
    have hS₀ := hS.1.mem_nhds ((hw e₀ _).2 (hj₀ e₀))
    have hd : DifferentiableAt ℂ (fun e => ω (j₀ e₀) e * (P (j₀ e₀) e)⁻¹) e₀ := by
      classical
      refine DifferentiableAt.mul (hS.2.differentiableAt hS₀) (DifferentiableAt.inv ?_ (hP _ _ (hj₀ e₀)))
      refine (HasFDerivAt.finsetProd fun k _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      refine DifferentiableAt.zpow (f := fun e => u.fr (j₀ e₀ k) (z k e)) ?_ (Or.inl (u.fr_ne _ _ (hj₀ e₀ k)))
      exact ((u.fr_hol _).differentiableAt ((u.hol _ 0).1.mem_nhds (hj₀ e₀ k))).comp e₀ (hz k e₀)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hS₀] with e he
    rw [hG _ _ e (hj₀ e) ((hw e _).1 he), div_eq_mul_inv]
  · beta_reduce
    rw [hG _ _ e (hj₀ e) h]
    exact (div_mul_cancel₀ _ (hP j e h)).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyPBScale

theorem appLE_constFn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {X Y : Scheme.{0}} {φ : Y ⟶ X}
    (p : X ⟶ Sp R) (p' : Y ⟶ Sp R') (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U)
    (a : R) : (φ.appLE U V h).hom (constFn p U a) = constFn p' V (f a) :=
  KeyVia.appLE_cst f p p' hφ h a

theorem resG_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a :=
  KeyVia.res_appLE (φ := p) (U := ⊤) (fun _ _ => trivial) h _

theorem lie_baseChange {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {G : Over (Sp R)} [GrpObj G]
    {G' : Over (Sp R')} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) {n m : ℕ}
    (e : m = n) (M : Matrix (Fin n) (Fin n) R) (v v' : Fin n → (epsR R ⟶ G)) (u u' : Fin m → (epsR R' ⟶ G'))
    (hv : ∀ i, IsLieComb (M i) v (v' i))
    (hu : ∀ i : Fin m, IsLieComb (fun j : Fin m => f (M (i.cast e) (j.cast e))) u (u' i))
    (huv : ∀ i, (u i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v (i.cast e)).left) (i : Fin m) :
    (u' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v' (i.cast e)).left := by
  subst e
  exact (lieComb_baseChange R R' f G G' φ h m v (v' i) (M i) u (u' i) huv (hv i)).2 (hu i)

theorem keyPB_scale : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (P : Out.PolAV (Sp R)) (hg rig hr th hth v hv th' hth' v' hv') (a : R) (M : Matrix (Fin P.g) (Fin P.g) R) (Q : Out.PolAV (Sp R')) (e : Q.g = P.g) (hgQ rigQ hrQ s hs u hu s' hs' u' hu'), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → (∀ i, LB.Sec.f s' i = constFn Q.A.hom _ (f a) * LB.Sec.f s i) → (∀ i : Fin Q.g, IsLieComb (fun j : Fin Q.g => f (M (i.cast e) (j.cast e))) u (u' i)) → KeyPB (⟨Q, hgQ, rigQ, hrQ, s, hs, u, hu⟩ : KeyIn R') (⟨P, hg, rig, hr, th, hth, v, hv⟩ : KeyIn R) f → KeyPB (⟨Q, hgQ, rigQ, hrQ, s', hs', u', hu'⟩ : KeyIn R') (⟨P, hg, rig, hr, th', hth', v', hv'⟩ : KeyIn R) f := by
  intro R R' _ _ f P hg rig hr th hth v hv th' hth' v' hv' a M Q e hgQ rigQ hrQ s hs u hu s' hs' u' hu' h₁ h₂ h₃ h₄
  rintro ⟨φ, he, w, hg', F, hp, hw, hrig, hsec, hF, hε, hlie⟩
  have hF' : F = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun b => (hF b).trans (by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]))
    (hε.trans (by ext <;> simp [Chart.dualMapR]))
  refine ⟨φ, he, w, hg', F, hp, hw, hrig, fun j i h => ?_, hF, hε, ?_⟩
  · have k := hsec j i h
    dsimp only at k ⊢
    rw [h₁, h₃, map_mul, map_mul, k, appLE_constFn f P.A.hom Q.A.hom hp.1.w, resG_constFn]
    exact mul_left_comm (G := Γ(Q.A.left, (P.L.pull φ).U j ⊓ Q.L.U i)) _ _ _
  · subst hF'
    exact lie_baseChange f hp e M v v' u u' h₂ h₄ hlie

end GlobalTheory.KeyPBScale
end
end

