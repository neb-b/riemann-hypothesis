module

public import Mathlib
public import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
public import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsGenTranslDiffComp
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_isGen_linComb_of_pull {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (f : Z ⟶ Y) (c : LB.Gen ((LB.LinComb L φ ε).pull f))
    (hc : c.IsGen) : ∃ d : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), d.IsGen := by
  have hle : ∀ j : K → L.ι, LB.wchart L (fun k => f ≫ φ k) j ≤
      LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => f) (fun _ => j) :=
    fun j _ hy => Set.mem_iInter.2 fun _ => LB.wchart_comp_le L f φ j hy
  refine ⟨⟨fun j => res (hle j) (LB.ts c (fun _ => j))⟩, ?_⟩
  refine (LB.isGen_iff L _).2 fun i j => ?_
  have key := congrArg (res (inf_le_inf (hle i) (hle j)))
    ((LB.isGen_iff (LB.LinComb L φ ε) c).1 hc (fun _ => i) (fun _ => j))
  have e := LB.lcg_pull (LB.LinComb L φ ε) f (fun _ => i) (fun _ => j)
  rw [LB.lcg_comp]
  refine (LB.res_res _ _ _).trans (((LB.res_res _ _ _).symm.trans key).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · exact (congrArg _ e).trans (LB.res_res _ _ _)
  · exact (LB.res_res _ _ _).trans (LB.res_res _ _ _).symm

theorem exists_isGen_translDiff_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left)
    {T T' : Over S} (x : T ⟶ A) (g : T' ⟶ T) (V : T.left.Opens)
    (hg : ∀ q, g.left q ∈ V)
    (c : LB.Gen ((Out.translDiff A L x).pull ((fst T A).left ⁻¹ᵁ V).ι)) (hc : c.IsGen) :
    ∃ d : LB.Gen (Out.translDiff A L (g ≫ x)), d.IsGen := by
  obtain ⟨d, hd⟩ := exists_isGen_linComb_of_pull L _ _ _ c hc
  have hr : Set.range (g ▷ A).left ⊆ Set.range ((fst T A).left ⁻¹ᵁ V).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ((g ▷ A).left ≫ (fst T A).left) y ∈ V
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
    exact hg _
  have hl := IsOpenImmersion.lift_fac ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr
  have h4 : ∃ w : LB.Gen (LB.LinComb L _ _), w.IsGen :=
    ⟨_, LB.isGen_pullGen L _ _ d hd (IsOpenImmersion.lift ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr)⟩
  have h3 : (fun k : Fin 2 => IsOpenImmersion.lift ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr ≫
      ((fst T A).left ⁻¹ᵁ V).ι ≫
        ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] k) =
      ![(lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left, (snd T' A).left] := by
    funext k
    rw [← Category.assoc, hl]
    fin_cases k
    · change (g ▷ A ≫ lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left =
        (lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left
      rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]
    · change (g ▷ A ≫ snd T A).left = (snd T' A).left
      rw [whiskerRight_snd]
  rw [h3] at h4
  exact h4

theorem kTriv_of_global : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB →
    (∀ (R : Type) [CommRing R] [Algebra ℂ R], ∀ (x : Over.mk (spMap (algebraMap ℂ R)) ⟶ A),
      (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1) → Out.KTriv A L := by
  intro A _ L _ _ H R _ t x hx
  have H' : ∀ (R' : CommRingCat.{0}) (t' : Spec R' ⟶ Sp ℂ) (y : Over.mk t' ⟶ A),
      (∃ c : LB.Gen (Out.translDiff A L y), c.IsGen) → y = 1 := by
    intro R' t'
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t'
    let _ : Algebra ℂ R' := φ.hom.toAlgebra
    exact H R'
  change x = 1
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨V, hp, c, hc⟩ := hx p
  obtain ⟨U, hU, hpU, hUV⟩ := exists_isAffineOpen_mem_and_subset (U := V) (x := p) hp
  refine ⟨U, hpU, ?_⟩
  let g : Over.mk (hU.fromSpec ≫ t) ⟶ Over.mk t := Over.homMk hU.fromSpec rfl
  have h1 : g ≫ x = g ≫ 1 := by
    rw [MonObj.comp_one]
    exact H' _ _ _ (exists_isGen_translDiff_comp A L x g V
      (fun q => hUV (hU.range_fromSpec.le ⟨q, rfl⟩)) c hc)
  have h2 : hU.fromSpec ≫ x.left = hU.fromSpec ≫ (1 : Over.mk t ⟶ A).left :=
    congrArg (·.left) h1
  rw [IsAffineOpen.fromSpec, Category.assoc, Category.assoc, cancel_epi] at h2
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsHomogeneousEvalOfMulMemSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

private theorem isWeightedHomogeneous_coeff_mul_rw1 {X ρ : Type} (b : ρ → X → ℂ) {k l : ℕ} {f g : X → ℂ}
    (hf : ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous k ∧
      ∀ z, f z = MvPolynomial.eval (fun c => b c z) G)
    (hg : ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous l ∧
      ∀ z, g z = MvPolynomial.eval (fun c => b c z) G) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous (k + l) ∧
      ∀ z, f z * g z = MvPolynomial.eval (fun c => b c z) G := by
  obtain ⟨G, hG, hfG⟩ := hf
  obtain ⟨H, hH, hgH⟩ := hg
  exact ⟨G * H, hG.mul hH, fun z => by rw [hfG, hgH, map_mul]⟩

private theorem exists_homogeneous_one_eval_of_mem_span {X ρ : Type} (b : ρ → X → ℂ) {f : X → ℂ}
    (hf : f ∈ Submodule.span ℂ (Set.range b)) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous 1 ∧
      ∀ z, f z = MvPolynomial.eval (fun c => b c z) G := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X (R := ℂ) i, fun z => by simp⟩
  | zero => exact ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun z => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨G, hG, hxG⟩ := hx
    obtain ⟨H, hH, hyH⟩ := hy
    exact ⟨G + H, hG.add hH, fun z => by simp [hxG, hyH]⟩
  | smul c x _ hx =>
    obtain ⟨G, hG, hxG⟩ := hx
    have hCG := (MvPolynomial.isHomogeneous_C (σ := ρ) c).mul hG
    rw [zero_add] at hCG
    exact ⟨MvPolynomial.C c * G, hCG, fun z => by simp [hxG]⟩

private theorem exists_homogeneous_eval_of_even_degree_monomial {X σ ρ : Type} (a : σ → X → ℂ) (b : ρ → X → ℂ)
    (hab : ∀ i j, a i * a j ∈ Submodule.span ℂ (Set.range b)) :
    ∀ (k : ℕ) (m : σ →₀ ℕ), m.degree = 2 * k →
      ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous k ∧
        ∀ z, (m.prod fun c e => a c z ^ e) = MvPolynomial.eval (fun c => b c z) G := by
  intro k
  induction k with
  | zero =>
    intro m hm
    rw [mul_zero, Finsupp.degree_eq_zero_iff] at hm
    subst hm
    exact ⟨1, MvPolynomial.isHomogeneous_one _ _, fun z => by simp⟩
  | succ k ih =>
    intro m hm
    classical
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : m = 0 := by ext x; exact h x
      rw [h0, map_zero] at hm
      omega
    have hle₁ : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m₁, rfl⟩ : ∃ m₁, m = m₁ + Finsupp.single i 1 :=
      ⟨_, (tsub_add_cancel_of_le hle₁).symm⟩
    rw [map_add (f := _), Finsupp.degree_single] at hm
    obtain ⟨j, hj⟩ : ∃ j, m₁ j ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : m₁ = 0 := by ext x; exact h x
      rw [h0, map_zero] at hm
      omega
    have hle₂ : Finsupp.single j 1 ≤ m₁ := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m₂, rfl⟩ : ∃ m₂, m₁ = m₂ + Finsupp.single j 1 :=
      ⟨_, (tsub_add_cancel_of_le hle₂).symm⟩
    rw [map_add (f := _), Finsupp.degree_single] at hm
    have hdeg : m₂.degree = 2 * k := by omega
    obtain ⟨G, hG, hGz⟩ := isWeightedHomogeneous_coeff_mul_rw1 b (ih m₂ hdeg) (exists_homogeneous_one_eval_of_mem_span b (hab j i))
    refine ⟨G, hG, fun z => ?_⟩
    rw [← hGz z, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp only [Finsupp.prod_single_index, pow_zero, pow_one, Pi.mul_apply]
    ring

theorem exists_isHomogeneous_eval_of_mul_mem_span {X σ ρ : Type} (a : σ → X → ℂ) (b : ρ → X → ℂ)
    (hab : ∀ i j, a i * a j ∈ Submodule.span ℂ (Set.range b)) (d : ℕ) (F : MvPolynomial σ ℂ)
    (hF : F.IsHomogeneous (2 * d)) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous d ∧
      ∀ z, MvPolynomial.eval (fun c => a c z) F = MvPolynomial.eval (fun c => b c z) G := by
  classical
  have hP : ∀ s : Finset (σ →₀ ℕ), s ⊆ F.support → ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous d ∧
      ∀ z, (∑ m ∈ s, F.coeff m * m.prod fun c e => a c z ^ e) =
        MvPolynomial.eval (fun c => b c z) G := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun z => by simp⟩
    | insert m s hms ih =>
      intro hsub
      obtain ⟨G, hG, hGz⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      have hm : m.degree = 2 * d := by
        rw [Finsupp.degree_eq_weight_one]
        exact hF (MvPolynomial.mem_support_iff.mp (hsub (Finset.mem_insert_self m s)))
      obtain ⟨H, hH, hHz⟩ := exists_homogeneous_eval_of_even_degree_monomial a b hab d m hm
      have hCH := (MvPolynomial.isHomogeneous_C (σ := ρ) (F.coeff m)).mul hH
      rw [zero_add] at hCH
      refine ⟨MvPolynomial.C (F.coeff m) * H + G, hCH.add hG, fun z => ?_⟩
      rw [Finset.sum_insert hms, hGz z, hHz z]
      simp
  obtain ⟨G, hG, hGz⟩ := hP F.support subset_rfl
  exact ⟨G, hG, fun z => by rw [MvPolynomial.eval_eq, ← hGz z]; rfl⟩

theorem theta_projectiveNormality_even :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∃ N : ℕ, 3 ≤ N ∧ ∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∃ N : ℕ, 3 ≤ N ∧ Even N ∧ (∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F)) := by
  intro hA hB hC g τ hτ
  obtain ⟨N, hN3, hNC⟩ := hC g τ hτ
  refine ⟨2 * N, by omega, even_two_mul N, fun d f hf => ?_⟩
  obtain ⟨F, hF, hFz⟩ := hNC (2 * d) f
    ⟨hf.1, fun n n' z => by rw [show N * (2 * d) = 2 * N * d by ring]; exact hf.2 n n' z⟩
  have hA' := (hA g τ hτ N (by omega)).1
  have hab : ∀ i j : Fin g → Fin N,
      (fun z : Fin g → ℂ => theta (fun k => ((i k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) *
        (fun z : Fin g → ℂ => theta (fun k => ((j k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∈
      Submodule.span ℂ (Set.range (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) =>
        theta (fun k => ((c k : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)) 0
          (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ))) := by
    intro i j
    refine hB g τ hτ (2 * N) (by omega) _ ⟨(hA' i).1.mul (hA' j).1, fun n n' z => ?_⟩
    have h1 := (hA' i).2 n n' z
    have h2 := (hA' j).2 n n' z
    beta_reduce at h1 h2 ⊢
    rw [Pi.mul_apply, Pi.mul_apply, h1, h2,
      show ∀ x : ℂ, eC (-((2 * N : ℕ) : ℂ) * x) = eC (-(N : ℂ) * x) * eC (-(N : ℂ) * x) from
        fun x => by unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  obtain ⟨G, hG, hGz⟩ := exists_isHomogeneous_eval_of_mul_mem_span
    (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
      theta (fun k => ((c k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))
    (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) =>
      theta (fun k => ((c k : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)) 0
        (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ))
    hab d F hF
  exact ⟨G, hG, fun z => (hFz z).trans (hGz z)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsLinearLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.EndoLinear

theorem fderiv_lifts {E E' M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] [Group M] (ex : E' → M) (hex : ∀ z w, ex (z + w) = ex z * ex w)
    (Λ : Submodule ℤ E') (hker : ∀ z, ex z = 1 ↔ z ∈ Λ) (hd : DiscreteTopology Λ)
    (a : E → M) (ha : ∀ z w, a (z + w) = a z * a w) (G : E → E') (h0 : G 0 = 0)
    (hG : DifferentiableAt ℂ G 0) (hev : ∀ᶠ w in 𝓝 0, ex (G w) = a w) (z : E) :
    ex (fderiv ℂ G 0 z) = a z := by
  have hc : ContinuousAt G 0 := hG.continuousAt
  have h2 : Tendsto (fun w : E => w + w) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun w : E => w + w) := by fun_prop
    simpa using this.tendsto 0
  have hG0 : Tendsto G (𝓝 0) (𝓝 0) := by simpa [h0] using hc.tendsto
  have hD : Tendsto (fun w : E => G (w + w) - (G w + G w)) (𝓝 0) (𝓝 0) := by
    simpa using (hG0.comp h2).sub (hG0.add hG0)
  have hmem : ∀ᶠ w in 𝓝 (0 : E), G (w + w) - (G w + G w) ∈ Λ := by
    filter_upwards [hev, h2.eventually hev] with w hw hw2
    rw [← hker]
    have h := hex (G (w + w) - (G w + G w)) (G w + G w)
    rw [sub_add_cancel, hw2, hex (G w), hw, ha] at h
    exact (mul_eq_right.mp h.symm)
  have hiso : ∀ᶠ y in 𝓝 (0 : E'), y ∈ Λ → y = 0 := by
    have ho : IsOpen ({0} : Set Λ) := isOpen_discrete _
    obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp ho
    have h0t : (0 : E') ∈ t := by
      have : (0 : Λ) ∈ Subtype.val ⁻¹' t := by rw [hts]; rfl
      exact this
    filter_upwards [ht.mem_nhds h0t] with y hy hyΛ
    have : (⟨y, hyΛ⟩ : Λ) ∈ Subtype.val ⁻¹' t := hy
    rw [hts] at this
    exact congrArg Subtype.val this
  have hdbl : ∀ᶠ w in 𝓝 (0 : E), G (w + w) = G w + G w := by
    filter_upwards [hmem, hD.eventually hiso] with w h1 h2
    exact sub_eq_zero.mp (h2 h1)
  set c : ℕ → ℂ := fun n => (2 : ℂ) ^ n with hcdef
  have hcn : Tendsto (fun n => ‖c n‖) atTop atTop := by
    simp only [hcdef, norm_pow, Complex.norm_ofNat]
    exact tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hz : Tendsto (fun n => (c n)⁻¹ • z) atTop (𝓝 0) := by
    have : Tendsto (fun n => (c n)⁻¹) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_inv]
      exact hcn.inv_tendsto_atTop
    simpa using this.smul_const z
  have hhalf : ∀ n, (c n)⁻¹ • z = (c (n + 1))⁻¹ • z + (c (n + 1))⁻¹ • z := by
    intro n
    rw [← add_smul]
    congr 1
    simp only [hcdef, pow_succ]
    field_simp
    norm_num
  have hlim : Tendsto (fun n => c n • G ((c n)⁻¹ • z)) atTop (𝓝 (fderiv ℂ G 0 z)) := by
    have := hG.hasFDerivAt.lim z hcn
    simpa [h0] using this
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hz.eventually (hdbl.and hev))
  have hconst : ∀ n, N ≤ n → c n • G ((c n)⁻¹ • z) = c N • G ((c N)⁻¹ • z) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [← ih, hhalf n, (hN (n + 1) (by omega)).1, ← two_smul ℂ, smul_smul]
      simp only [hcdef, pow_succ]
  have hF : fderiv ℂ G 0 z = c N • G ((c N)⁻¹ • z) := by
    refine tendsto_nhds_unique hlim ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn using (hconst n hn).symm
  have hpow : ∀ (n : ℕ) (x : E') (y : E), ex x = a y → ex (c n • x) = a (c n • y) := by
    intro n x y h
    induction n with
    | zero => simpa [hcdef] using h
    | succ n ih =>
      have e : c (n + 1) = c n + c n := by simp only [hcdef, pow_succ]; ring
      rw [e, add_smul, add_smul, hex, ha, ih]
  rw [hF, hpow N _ _ (hN N le_rfl).2, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]

theorem exists_linear_lift :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), (∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)), (∀ (U : (A).left.Opens) (f : Γ((A).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 → ∃ G : (Fin n → ℂ) → (Fin g → ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, u.ex (G w) = a w) → ∀ f : A ⟶ A, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f) := by
  intro hval A _ L g u hlift f hf
  have h0 : u.ex 0 = 1 := (u.ker 0).mpr u.Λ.zero_mem
  obtain ⟨G, hG0, hGa, hGe⟩ := hlift g (fun z => u.ex z ≫ f) (by
    intro U s
    have hset : {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (u.ex w ≫ f).left ⁻¹ᵁ U} =
        {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (f.left ⁻¹ᵁ U)} := by
      ext w
      simp
    have hfun : (fun w => valAt' (u.ex w ≫ f).left U s) =
        fun w => valAt' (u.ex w).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s) := by
      funext w
      exact ((hval A.left (u.ex w).left).2.2.2.1 A.left f.left U s).symm
    rw [hset, hfun]
    exact u.hol _ _) (by simp only [h0]; exact MonObj.one_comp f)
  refine ⟨(fderiv ℂ G 0).toLinearMap, fun z => ?_⟩
  exact fderiv_lifts u.ex u.ex_add u.Λ u.ker u.discrete (fun z => u.ex z ≫ f)
    (fun z w => by simp only [u.ex_add]; exact MonObj.mul_comp _ _ f) G hG0 hGa.differentiableAt hGe z

end GlobalTheory.EndoLinear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsAHOfPolarisation
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

def thetaZeroSec {X : Scheme.{0}} (L : LB X) : L.Sec where
  f _ := 0
  compat := by intros; simp

theorem valAt'_zero_fn {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) : valAt' x U 0 = 0 := by
  unfold valAt'
  split_ifs with h
  · simp [valAt]
  · rfl

theorem isAH_of_polarisation :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (θ : (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Injective Ef → Differentiable ℂ θ → θ ≠ 0 → (∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) → ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ (P : Out.PolAV (Sp ℂ)) (n : ℕ), 1 ≤ n → ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ a : Fin (n ^ P.g) → ℂ, (∀ j, ∑ i, constFn P.A.hom _ (a i) * (s i).f j = 0) → a = 0) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef → u.IsAH Hm χ) := by
  intro _ hpos hsec hthe P u Hm χ Ef hAH hbij
  obtain ⟨hH, hχ, hE, hfr⟩ := hAH
  refine ⟨hH, ?_, hχ, hfr⟩

  obtain ⟨s, hs⟩ := hsec P 1 le_rfl
  have hone : ∀ i j : Fin (1 ^ P.g), i = j := fun i j =>
    Fin.ext (by
      have hi : (i : ℕ) < 1 := lt_of_lt_of_eq i.isLt (one_pow _)
      have hj : (j : ℕ) < 1 := lt_of_lt_of_eq j.isLt (one_pow _)
      omega)
  let i0 : Fin (1 ^ P.g) := ⟨0, by rw [one_pow]; exact Nat.one_pos⟩
  have hcorr := hthe P u Hm χ Ef ⟨hH, hχ, hE, hfr⟩ 1
  obtain ⟨θ, ⟨hθ, hfn⟩, -⟩ := hcorr.1 (s i0)

  have hθne : θ ≠ 0 := by
    rintro rfl
    have hz : u.IsFnPow 1 (thetaZeroSec (lbPow P.L 1)) 0 := by
      intro j z _
      rw [Pi.zero_apply, zero_mul]
      exact valAt'_zero_fn _ _
    have hs0 : s i0 = thetaZeroSec (lbPow P.L 1) := hcorr.2 0 _ _ hfn hz
    have hall : ∀ i, s i = thetaZeroSec (lbPow P.L 1) := fun i => by rw [hone i i0, hs0]
    have h1 := hs (fun _ => 1) (fun j => Finset.sum_eq_zero (fun i _ => by rw [hall i]; exact mul_zero _))
    exact absurd (congrFun h1 i0) (by simp)

  exact hpos P.g u.Λ u.discrete u.full Hm χ Ef θ hH hχ hE hbij.1 hθ.1 hθne
    (fun l z => by have h := hθ.2 l z; rw [pow_one] at h; exact h)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedTensorObjComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem isReduced_tensorObj_complex :
    (∀ (X Y : Over (Sp ℂ)), IsReduced X.left → IsReduced Y.left → LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom → IsReduced (X ⊗ Y).left) := by
  intro X Y hX hY hfX hfY

  have : GeometricallyReduced X.hom :=
    ReducedSubgroup.geometricallyReduced_of_perfectField (k := ℂ) X.hom
  have : Flat X.hom := inferInstance
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  change IsReduced (Limits.pullback X.hom Y.hom)
  infer_instance

end GlobalTheory
end

