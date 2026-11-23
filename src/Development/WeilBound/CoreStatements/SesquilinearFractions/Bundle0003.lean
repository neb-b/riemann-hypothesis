module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsNsmulMemSpanFullFamily
section
open NumberField

namespace PositivityTheory.Xgf

theorem exists_nsmul_mem_span_full_family {E : Type} [Field E] [NumberField E] {M : Type} [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M] {I : Type} [Fintype I] (e : I → M)
    (hcard : Fintype.card I = Module.finrank (𝓞 E) M) (he : LinearIndependent (𝓞 E) e) :
    ∃ n : ℕ, 0 < n ∧ ∀ y : M, n • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
  classical
  set N := Submodule.span (𝓞 E) (Set.range e) with hN
  have htor : ∀ y : M, ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ N := by
    intro y
    have hnot : ¬ LinearIndependent (𝓞 E) (Sum.elim e (fun _ : Unit => y)) := by
      intro hli
      have := hli.fintype_card_le_finrank
      rw [Fintype.card_sum, Fintype.card_unit, hcard] at this
      omega
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton] at hg
    by_cases hc : g (Sum.inr ()) = 0
    · exfalso
      rw [hc, zero_smul, add_zero] at hg
      have h0 := Fintype.linearIndependent_iff.mp he (fun j => g (Sum.inl j)) hg
      rcases i with j | ⟨⟩
      · exact hi (h0 j)
      · exact hi hc
    · refine ⟨g (Sum.inr ()), hc, ?_⟩
      rw [eq_neg_of_add_eq_zero_right hg]
      exact N.neg_mem (N.sum_mem fun j _ => N.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩))
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := M)
  choose c hc0 hcN using htor
  have ha0 : (∏ y ∈ s, c y) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun y _ => hc0 y
  have haN : ∀ y : M, (∏ y ∈ s, c y) • y ∈ N := by
    intro y
    have hy : y ∈ Submodule.span (𝓞 E) (s : Set M) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
        rw [← Finset.prod_erase_mul s c hx, mul_smul]
        exact N.smul_mem _ (hcN x)
    | zero => simp
    | add x z _ _ hx hz => rw [smul_add]; exact N.add_mem hx hz
    | smul b x _ hx => rw [smul_comm]; exact N.smul_mem b hx
  have hI : Ideal.span ({∏ y ∈ s, c y} : Set (𝓞 E)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  refine ⟨Ideal.absNorm (Ideal.span ({∏ y ∈ s, c y} : Set (𝓞 E))),
    Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun y => ?_⟩
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span ({∏ y ∈ s, c y} : Set (𝓞 E))))
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hb, mul_smul]
  exact N.smul_mem b (haN y)

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GBridge
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

private theorem pt_zero_lemma {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

private theorem LieModel_pt_sum_eq_prod {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) :
    ∀ (n : ℕ) (v : Fin n → U), M.pt (∑ k, v k) = (List.ofFn fun k => M.pt (v k)).prod := by
  intro n
  induction n with
  | zero => intro v; simp [pt_zero_lemma M]
  | succ n ih =>
    intro v
    rw [Fin.sum_univ_succ, M.add, ih, List.ofFn_succ, List.prod_cons]

private theorem isComb_pt_iff_eq_pt_sum {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) (n : ℕ) (c : Fin n → R) (u : Fin n → U)
    (w : epsAt x ⟶ G) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k) := by
  unfold GlobalTheory.CompanionTheory.Ar.Fl.IsComb
  rw [LieModel_pt_sum_eq_prod M]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : v = fun i => M.pt (c i • u i) := by
      funext i
      apply Over.OverMorphism.ext
      rw [hv i, M.smul]
    rw [hv']
  · intro h
    refine ⟨fun i => M.pt (c i • u i), fun i => ?_, h⟩
    rw [M.smul]

private theorem isEigVec_pt_iff_mem_eigSp {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) {O : Type} [CommRing O] (act : OAct O G)
    (ρ : O →+* Module.End R U) (τ : O →+* R) (hM : M.IsActOf act.act ρ) (u : U) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ := by
  unfold GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec eigSp
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  constructor
  · rintro ⟨-, h⟩ a
    apply M.inj
    apply Over.OverMorphism.ext
    rw [hM a u, M.smul, h a]
  · intro h
    refine ⟨M.tan u, fun a => ?_⟩
    rw [← hM a u, h a, M.smul]

theorem lie_model_eigenvectors_action : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (U : Type) [AddCommGroup U] [Module R U] (M : LieModel G x U), (∀ (n : ℕ) (c : Fin n → R) (u : Fin n → U) w, IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k)) ∧ ∀ (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End R U) (τ : O →+* R), M.IsActOf act.act ρ → (∀ u, IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ) ∧ ∀ (n : ℕ) (u : Fin n → U), IsEigFrame act x τ (fun k => M.pt (u k)) ↔ LinearIndependent R u ∧ Submodule.span R (Set.range u) = eigSp ρ τ := by
  intro S R _ G _ x U _ _ M
  refine ⟨fun n c u w => isComb_pt_iff_eq_pt_sum M n c u w, fun O _ act ρ τ hM => ⟨fun u => isEigVec_pt_iff_mem_eigSp M act ρ τ hM u, fun n u => ?_⟩⟩
  unfold GlobalTheory.CompanionTheory.Ar.Fl.IsEigFrame
  constructor
  · rintro ⟨hu, huniq⟩
    have hu' : ∀ i, u i ∈ eigSp ρ τ := fun i => (isEigVec_pt_iff_mem_eigSp M act ρ τ hM (u i)).mp (hu i)
    have hex : ∀ e ∈ eigSp ρ τ, ∃! c : Fin n → R, e = ∑ k, c k • u k := by
      intro e he
      obtain ⟨c, hc, huq⟩ := huniq (M.pt e) ((isEigVec_pt_iff_mem_eigSp M act ρ τ hM e).mpr he)
      exact ⟨c, M.inj ((isComb_pt_iff_eq_pt_sum M n c u _).mp hc),
        fun c' hc' => huq c' ((isComb_pt_iff_eq_pt_sum M n c' u _).mpr (congrArg M.pt hc'))⟩
    refine ⟨?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      obtain ⟨c, -, huq⟩ := hex 0 (Submodule.zero_mem _)
      have hg0 : g = 0 := (huq g hg.symm).trans (huq 0 (by simp)).symm
      rw [hg0]
      rfl
    · apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hu' i
      · intro e he
        obtain ⟨c, hc, -⟩ := hex e he
        rw [hc]
        exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro ⟨hli, hsp⟩
    have hu' : ∀ i, u i ∈ eigSp ρ τ := fun i => hsp ▸ Submodule.subset_span ⟨i, rfl⟩
    refine ⟨fun i => (isEigVec_pt_iff_mem_eigSp M act ρ τ hM (u i)).mpr (hu' i), fun w hw => ?_⟩
    have ht : IsTanAt G x w := by
      obtain ⟨h, -⟩ := hw
      exact h
    obtain ⟨e, rfl⟩ := M.onto w ht
    have he : e ∈ eigSp ρ τ := (isEigVec_pt_iff_mem_eigSp M act ρ τ hM e).mp hw
    rw [← hsp] at he
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp he
    refine ⟨c, (isComb_pt_iff_eq_pt_sum M n c u _).mpr (congrArg M.pt hc.symm), fun c' hc' => ?_⟩
    have h1 : e = ∑ k, c' k • u k := M.inj ((isComb_pt_iff_eq_pt_sum M n c' u _).mp hc')
    have h2 : ∑ k, (c' k - c k) • u k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← h1, hc, sub_self]
    funext k
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h2 k)

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GGramComb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf.HermitianFormSum

variable {S : Scheme.{0}}

theorem one_left (G : Over S) [GrpObj G] (Y : Over S) : (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem hermForm_sum {g n m : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : Fin n → ℂ) (b : Fin m → ℂ)
    (W : Fin n → Fin g → ℂ) (W' : Fin m → Fin g → ℂ) :
    hermForm Hm (∑ i, a i • W i : Fin g → ℂ) (∑ j, b j • W' j : Fin g → ℂ) = ∑ i, ∑ j, a i * star (b j) * hermForm Hm (W i) (W' j) := by
  simp only [hermForm, dotProduct, mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply, star_sum,
    star_mul', Finset.mul_sum, Finset.sum_mul]
  have e1 : ∀ x x1, (∑ x_2 : Fin m, ∑ i : Fin n, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1)))) =
      ∑ i : Fin n, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))) := fun x x1 => Finset.sum_comm
  simp only [e1]
  have e2 : ∀ x, (∑ x1 : Fin g, ∑ i : Fin n, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1)))) =
      ∑ i : Fin n, ∑ x1 : Fin g, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))) := fun x => Finset.sum_comm
  simp only [e2]
  rw [Finset.sum_comm (f := fun (x : Fin g) (i : Fin n) => ∑ x1 : Fin g, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e3 : ∀ x, (∑ x1 : Fin g, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1)))) =
      ∑ x_2 : Fin m, ∑ x1 : Fin g, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))) := fun x => Finset.sum_comm
  simp only [e3]
  rw [Finset.sum_comm (f := fun (x : Fin g) (x_2 : Fin m) => ∑ x1 : Fin g, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end PositivityTheory.Xgf.HermitianFormSum

namespace PositivityTheory.Xgf

open PositivityTheory.Xgf.HermitianFormSum in
theorem hodge_gram_linear_combination : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n n' : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n' → (epsAt x ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n') (Fin n) ℂ), (∀ k, IsTanAt G x (v k)) → IsHodgeGram G L x v Γ → (∀ k, IsComb (A k) v (v' k)) → IsHodgeGram G L x v' (A * Γ * Aᴴ) := by
  intro S G _ L x n n' v v' Γ A hT hG hC
  obtain ⟨Q, ψ, v₁, u, Hm, χ, W, hPB, hLB, hAH, hv, hΓ⟩ := hG
  have hη : (η[Q.A] : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A).left ≫ ψ = x ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
    have hw : ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A).left ≫ ψ) ≫ G.hom = (Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ x)).hom := by
      rw [Category.assoc, hPB.1.w, ← Category.assoc, Over.w]
      rfl
    let a₀ : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ x) ⟶ G := Over.homMk ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A).left ≫ ψ) hw
    have hm := hPB.2 (𝟙_ (Over (Sp ℂ))) 1 1 a₀ a₀ rfl rfl
    rw [_root_.mul_one] at hm
    have h1 : a₀ * a₀ = a₀ * 1 := by
      rw [_root_.mul_one]
      exact Over.OverMorphism.ext hm
    have h2 := congrArg (fun h => h.left) (mul_left_cancel h1)
    simp only [a₀, Over.homMk_left, one_left] at h2
    simpa using h2
  have hunit : ∀ T : Over (Sp ℂ), (1 : T ⟶ Q.A).left ≫ ψ = (1 : Over.mk (T.hom ≫ x) ⟶ G).left := by
    intro T
    rw [one_left, one_left, Category.assoc, hη]
    simp
  have hprod : ∀ (k : ℕ) (uu : Fin k → (epsR ℂ ⟶ Q.A)) (dd : Fin k → (epsAt x ⟶ G)),
      (∀ i, (dd i).left = (uu i).left ≫ ψ) → (List.ofFn dd).prod.left = (List.ofFn uu).prod.left ≫ ψ := by
    intro k
    induction k with
    | zero => intro uu dd _; simpa using (hunit (epsR ℂ)).symm
    | succ k ih =>
      intro uu dd h
      rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
      exact hPB.2 (epsR ℂ) _ _ _ _ (h 0) (ih _ _ fun i => h i.succ)
  have hsp : ∀ (c : ℂ), spMap (epsScaleR c) ≫ (epsR ℂ).hom = (epsR ℂ).hom := by
    intro c
    simp only [epsR, Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext z
    · simp [epsScaleR]
    · simp [epsScaleR]
  have htan : ∀ i, IsTangent (v₁ i) := by
    intro i
    apply hPB.1.hom_ext
    · rw [Category.assoc, (hv i).1, hT i, one_left, hη]
      rfl
    · rw [Category.assoc, Over.w, Over.w]
      simp only [epsR, Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have e : ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
        ext z; simp
      erw [e, CommRingCat.ofHom_id, Spec.map_id]
      rfl
  choose u' hu' hv' using hC
  let uu : ∀ k, Fin n → (epsR ℂ ⟶ Q.A) := fun k i =>
    Over.homMk (spMap (epsScaleR (A k i)) ≫ (v₁ i).left) (by rw [Category.assoc, Over.w]; exact hsp _)
  refine ⟨Q, ψ, fun k => (List.ofFn (uu k)).prod, u, Hm, χ, fun k => ∑ i, A k i • W i, hPB, hLB, hAH,
    fun k => ⟨?_, ?_⟩, fun k l => ?_⟩
  · rw [hv' k]
    exact (hprod n (uu k) (u' k) fun i => by
      rw [hu' k i]
      show _ = (spMap (epsScaleR (A k i)) ≫ (v₁ i).left) ≫ ψ
      rw [Category.assoc, (hv i).1]
      rfl).symm
  · exact GlobalTheory.isDiff_sum_smul_of_isLieComb Q.A Q.isAb Q.L Q.g n u v₁ W (A k) _ htan (fun i => (hv i).2)
      ⟨uu k, fun i => rfl, rfl⟩
  · rw [hermForm_sum]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hΓ, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.star_def]
    ring

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GGramPush
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder CategoryTheory.Obj

namespace PositivityTheory.Xgf.ChartPullbackComposition

variable {X X' X'' : Scheme.{0}}

def chartPullComp (L : LB X) (φ : X' ⟶ X) (ψ : X'' ⟶ X') : ChartPull (L.pull (ψ ≫ φ)) (L.pull φ) ψ where
  idx J := J
  le J y hy := (mem_pull (F := φ)).2 ((mem_pull (F := ψ ≫ φ)).1 hy)
  g y J J' hj hj' := by
    have h1 : ψ y ∈ (L.pull φ).U J := (mem_pull (F := φ)).2 ((mem_pull (F := ψ ≫ φ)).1 hj)
    have h2 : ψ y ∈ (L.pull φ).U J' := (mem_pull (F := φ)).2 ((mem_pull (F := ψ ≫ φ)).1 hj')
    refine (gm_pull_g L (ψ ≫ φ) (𝟙 _) y J J' hj hj').trans ?_
    refine Eq.trans ?_ (gm_pull_g L φ ψ y J J' h1 h2).symm
    rw [Category.id_comp]

end PositivityTheory.Xgf.ChartPullbackComposition

namespace PositivityTheory.Xgf

open PositivityTheory.Xgf.ChartPullbackComposition in
theorem hodge_gram_invariant_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (n : ℕ) (v' : Fin n → (epsAt x' ⟶ t'.G)) (v : Fin n → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x = x' ≫ f → (∀ k, (v k).left = (v' k).left ≫ m.φ) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  intro E _ _ _ H S S' t t' f m x' x n v' v Γ hx hv
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull m.φ) := ⟨w₀, hw₀⟩

  have hpull : ∀ {Z : Scheme.{0}} (ψ' : Z ⟶ t'.G.left), LBIso (t'.PP.L.pull ψ') (t.PP.L.pull (ψ' ≫ m.φ)) :=
    fun ψ' => LBIso.chartPull (chartPullPull t'.PP.L ψ' ψ' rfl) (chartPullComp t.PP.L m.φ ψ') hL
  constructor
  · rintro ⟨Q, ψ', v₁, u, Hm, χ, W, hPB, hLB, hAH, hv₁, hΓ⟩
    refine ⟨Q, ψ' ≫ m.φ, v₁, u, Hm, χ, W, (hPB.comp m.cart).congr hx.symm rfl, ?_, hAH, fun i => ⟨?_, (hv₁ i).2⟩, hΓ⟩
    · exact LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB t'.PP.isLB _) Q.isLB (LBIso.symm (hpull ψ')) hLB
    · rw [← Category.assoc, (hv₁ i).1, hv i]
  · rintro ⟨Q, ψ, v₁, u, Hm, χ, W, hPB, hLB, hAH, hv₁, hΓ⟩
    have hP := ((isGrpPullback_pullback t'.G x').comp m.cart).congr hx.symm rfl
    obtain ⟨e, he, heψ⟩ := grpPullback_iso hPB hP
    have hψ' : IsGrpPullback Q.A t'.G x' (e.hom.left ≫ pullback.fst t'.G.hom x') :=
      ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback t'.G x')).congr (Category.id_comp x') rfl
    have hcomp : (e.hom.left ≫ pullback.fst t'.G.hom x') ≫ m.φ = ψ := by
      rw [Category.assoc]; exact heψ
    refine ⟨Q, e.hom.left ≫ pullback.fst t'.G.hom x', v₁, u, Hm, χ, W, hψ', ?_, hAH, fun i => ⟨?_, (hv₁ i).2⟩, hΓ⟩
    · refine LBIso.trans (pull_isLB t'.PP.isLB _) (pull_isLB t.PP.isLB _) Q.isLB (hpull _) ?_
      rw [hcomp]
      exact hLB
    · apply m.cart.1.hom_ext
      · rw [Category.assoc, hcomp, (hv₁ i).1, hv i]
      · rw [Category.assoc, hψ'.1.w, ← Category.assoc, Over.w, Over.w]
        rfl

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntA
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

variable {S : Scheme.{0}} {R : Type} [CommRing R]

theorem pt_zero {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem pt_nsmul {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) (e : E) : ∀ N : ℕ, M.pt (N • e) = M.pt e ^ N
  | 0 => by rw [zero_smul, pt_zero, pow_zero]
  | N + 1 => by rw [succ_nsmul, M.add, pt_nsmul M e N, pow_succ]

theorem comp_pow' {X A : Over S} [GrpObj A] (x : X ⟶ A) (g : A ⟶ A) : ∀ N : ℕ, x ≫ g ^ N = (x ≫ g) ^ N
  | 0 => by rw [pow_zero, pow_zero, MonObj.comp_one]
  | N + 1 => by rw [pow_succ, pow_succ, comp_mul, comp_pow' x g N]

def castM {G : Over S} [GrpObj G] {x x' : Sp R ⟶ S} (h : x = x') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) : LieModel G x' E := h ▸ M

theorem castM_left {G : Over S} [GrpObj G] {x x' : Sp R ⟶ S} (h : x = x') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) (e : E) : ((castM h M).pt e).left = (M.pt e).left := by
  subst h; rfl

def toAt {A : Over (Sp R)} (v : epsR R ⟶ A) : epsAt (𝟙 (Sp R)) ⟶ A :=
  Over.homMk v.left (by simp [Over.w v])

theorem toAt_left {A : Over (Sp R)} (v : epsR R ⟶ A) : (toAt v).left = v.left := rfl

theorem toAt_tan {A : Over (Sp R)} [GrpObj A] (v : epsR R ⟶ A) (hv : IsTangent v) : IsTanAt A (𝟙 (Sp R)) (toAt v) := by
  unfold IsTanAt
  rw [toAt_left]
  unfold IsTangent at hv
  rw [hv]
  first
  | (rw [Hom.one_def]; simp)
  | simp [Hom.one_def]
  | (rw [Hom.one_def, Over.comp_left]; congr 1; simp)
  | rfl

end PositivityTheory.Xgf.isogeny_decomposition_product

end
end

