module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
public import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.EvalDivOfIsHomogeneous
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace ThetaQuotient

theorem eval_div_of_isHomogeneous {σ : Type*} {F : MvPolynomial σ ℂ} {d : ℕ} (hF : F.IsHomogeneous d) (v : σ → ℂ)
    (t : ℂ) : MvPolynomial.eval (fun i => v i / t) F = MvPolynomial.eval v F / t ^ d := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.sum_div]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hd, mul_div_assoc]

theorem valAt'_eval₂ {σ : Type*} {X : Over (Sp ℂ)} (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) {U : X.left.Opens}
    (h : ⊤ ≤ x.left ⁻¹ᵁ U) (r : σ → Γ(X.left, U)) (F : MvPolynomial σ ℂ) :
    valAt' x.left U (MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) = MvPolynomial.eval (fun i => valAt' x.left U (r i)) F := by
  have hx : x.left ≫ X.hom = 𝟙 _ := Over.w x
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C, MvPolynomial.eval_C]
    exact valAt'_constFn x.left X.hom hx U a h
  | add p q hp hq => rw [MvPolynomial.eval₂_add, map_add (f := _), valAt'_add, hp, hq]
  | mul_X p i hp => rw [MvPolynomial.eval₂_mul, map_mul, valAt'_mul, hp, MvPolynomial.eval₂_X, MvPolynomial.eval_X]

theorem exists_glue_of_values {X : Over (Sp ℂ)}
    (hext : ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)),
      (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f')
    {κ : Type} (V : κ → X.left.Opens) (s : ∀ i, Γ(X.left, V i)) (a : (𝟙_ (Over (Sp ℂ)) ⟶ X) → ℂ)
    (hs : ∀ i x, ⊤ ≤ x.left ⁻¹ᵁ V i → valAt' x.left (V i) (s i) = a x) :
    ∃ φ : Γ(X.left, ⨆ i, V i), ∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ x.left ⁻¹ᵁ (⨆ i, V i) →
      valAt' x.left (⨆ i, V i) φ = a x := by
  obtain ⟨φ, hφ, -⟩ := X.left.sheaf.existsUnique_gluing V s (by
    intro i j
    refine hext _ _ _ fun x hx => ?_
    obtain ⟨hi, hj⟩ := (top_le_preimage_inf x.left _ _).1 hx
    refine (valAt'_map x.left _ (s i) hx).trans (Eq.trans ?_ (valAt'_map x.left _ (s j) hx).symm)
    rw [hs i x hi, hs j x hj])
  refine ⟨φ, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 ((top_le_preimage_iff_mem x.left _).1 hx)
  have hi' := (top_le_preimage_iff_mem x.left _).2 hi
  rw [← hs i x hi', ← hφ i]
  exact (valAt'_map x.left _ φ hi').symm

theorem exists_div_basicOpen {X : Scheme.{0}} {U : X.Opens} (f g : Γ(X, U)) :
    ∃ s : Γ(X, X.basicOpen g), ∀ x : Sp ℂ ⟶ X, ⊤ ≤ x ⁻¹ᵁ X.basicOpen g →
      valAt' x (X.basicOpen g) s = valAt' x U f / valAt' x U g := by
  have hunit : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g) :=
    X.toRingedSpace.isUnit_res_basicOpen g
  obtain ⟨u, hu⟩ := hunit
  refine ⟨(X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom f * (u⁻¹).val, fun x hx => ?_⟩
  have h1 : valAt' x (X.basicOpen g) u.val = valAt' x U g := by
    rw [hu]
    exact valAt'_map x _ g hx
  rw [valAt'_mul, valAt'_map x _ f hx, div_eq_mul_inv, ← h1]
  congr 1
  exact valAt'_units_inv x hx u

end ThetaQuotient


open ThetaQuotient in
theorem theta_quotient_regular : (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → (∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F) → ∀ (X : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧ (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z))) := by
  intro hext g τ _ N _ hpoly X ex D ⟨hint, hprop, hsurj, _, _, hD, hcov⟩ d p q hp hq
  have hext' := hext X inferInstance inferInstance
  obtain ⟨P, hP, hPv⟩ := hpoly d p hp
  obtain ⟨Q, hQ, hQv⟩ := hpoly d q hq
  generalize hθ : (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
    theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) = θ
  have hθ' : ∀ c z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) = θ c z :=
    fun c z => congrFun (congrFun hθ c) z
  simp only [hθ'] at hD hPv hQv
  have hmem : ∀ c z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ θ c z ≠ 0 := fun c => (hD c).2.2.1
  choose r hr using fun c => (hD c).2.2.2
  have hφ : ∀ (F : MvPolynomial (Fin g → Fin N) ℂ), F.IsHomogeneous d → ∀ c, ∃ φ : Γ(X.left, D c), ∀ z, θ c z ≠ 0 →
      valAt' (ex z).left (D c) φ = MvPolynomial.eval (fun c' => θ c' z) F / θ c z ^ d := by
    intro F hF c
    refine ⟨_, fun z hz => (valAt'_eval₂ (ex z) ((hmem c z).2 hz) (r c) F).trans ?_⟩
    rw [← eval_div_of_isHomogeneous hF]
    congr 2
    funext c'
    exact (hr c).1 c' z hz
  choose φp hφp using hφ P hP
  choose φq hφq using hφ Q hQ
  simp only [← hPv, ← hQv] at hφp hφq
  choose s hs using fun c => exists_div_basicOpen (φp c) (φq c)
  have hV : ∀ c z, ⊤ ≤ (ex z).left ⁻¹ᵁ X.left.basicOpen (φq c) ↔ θ c z ≠ 0 ∧ q z ≠ 0 := by
    intro c z
    rw [top_le_preimage_basicOpen_iff]
    constructor
    · intro h
      have h1 := (hmem c z).1 (top_le_preimage_of_valAt'_ne_zero _ h)
      rw [hφq c z h1] at h
      exact ⟨h1, fun h0 => h (by rw [h0, zero_div])⟩
    · rintro ⟨h1, h2⟩
      rw [hφq c z h1]
      exact div_ne_zero h2 (pow_ne_zero _ h1)
  have hsv : ∀ c z, ⊤ ≤ (ex z).left ⁻¹ᵁ X.left.basicOpen (φq c) →
      valAt' (ex z).left _ (s c) = p z / q z := by
    intro c z h
    obtain ⟨h1, _⟩ := (hV c z).1 h
    rw [hs c _ h, hφp c z h1, hφq c z h1, div_div_div_cancel_right₀ (pow_ne_zero _ h1)]
  choose σ hσ using hsurj
  obtain ⟨φ, hφ⟩ := exists_glue_of_values hext' (fun c => X.left.basicOpen (φq c)) s (fun x => p (σ x) / q (σ x))
    (fun c x hx => by
      have := hsv c (σ x) (by rw [hσ]; exact hx)
      rwa [hσ] at this)
  have hU : ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ (⨆ c, X.left.basicOpen (φq c)) ↔
      ∃ c, ⊤ ≤ (ex z).left ⁻¹ᵁ X.left.basicOpen (φq c) := by
    intro z
    refine (top_le_preimage_iff_mem _ _).trans (TopologicalSpace.Opens.mem_iSup.trans (exists_congr fun c => ?_))
    exact (top_le_preimage_iff_mem _ _).symm
  have hU' : ∀ z, q z ≠ 0 → ∃ c, ⊤ ≤ (ex z).left ⁻¹ᵁ X.left.basicOpen (φq c) := by
    intro z hz
    have : (ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ c, D c := by rw [hcov]; trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact ⟨c, (hV c z).2 ⟨(hmem c z).1 ((top_le_preimage_iff_mem _ _).2 hc), hz⟩⟩
  refine ⟨_, φ, fun z => ⟨⟨fun h => ?_, fun h => (hU z).2 (hU' z h)⟩, fun h => ?_⟩⟩
  · obtain ⟨c, hc⟩ := (hU z).1 h
    exact ((hV c z).1 hc).2
  · obtain ⟨c, hc⟩ := hU' z h
    rw [hφ _ ((hU z).2 ⟨c, hc⟩), ← hsv c z hc]
    have := hsv c (σ (ex z)) (by rw [hσ]; exact hc)
    rw [hσ] at this
    exact this.symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTopLePreimageOfISupEqTop
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace TorusEnd

theorem top_le_preimage_finset_inf {X : Scheme.{0}} {κ : Type*} (x : Sp ℂ ⟶ X) (s : Finset κ) (U : κ → X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (s.inf U) ↔ ∀ i ∈ s, ⊤ ≤ x ⁻¹ᵁ U i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih => rw [Finset.inf_insert, top_le_preimage_inf, ih, Finset.forall_mem_insert]

theorem exists_top_le_preimage_of_iSup_eq_top {X : Scheme.{0}} {κ : Type*} (x : Sp ℂ ⟶ X) (U : κ → X.Opens)
    (h : ⨆ i, U i = ⊤) : ∃ i, ⊤ ≤ x ⁻¹ᵁ U i := by
  have : x (default : PrimeSpectrum ℂ) ∈ ⨆ i, U i := by rw [h]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨i, (top_le_preimage_iff_mem x _).2 hi⟩

theorem valAt'_eval₂ {X : Over (Sp ℂ)} {κ : Type*} (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) (U : X.left.Opens)
    (h : ⊤ ≤ x.left ⁻¹ᵁ U) (r : κ → Γ(X.left, U)) (P : MvPolynomial κ ℂ) :
    valAt' x.left U (MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r P) = MvPolynomial.eval (fun i => valAt' x.left U (r i)) P := by
  have hc : (valAtHom x.left U h).comp (RingHom.comp (X.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) = RingHom.id ℂ := by
    ext a
    have := valAt'_constFn x.left X.hom (Over.w x) U a h
    rw [valAt'_eq_valAtHom _ h] at this
    exact this
  rw [valAt'_eq_valAtHom _ h, MvPolynomial.hom_eval₂, hc]
  simp only [valAt'_eq_valAtHom _ h]
  rfl

theorem hom_ext_of_points {X Y : Over (Sp ℂ)}
    (H : ∀ F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D : X.left.Opens), ⊤ ≤ (y).left ⁻¹ᵁ U ∧ IsAffineOpen D ∧ (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧ ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → valAt' y'.left U ρ = valAt' (F y').left D φ) → ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y)
    {m m' : Y ⟶ X} (h : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ Y, y ≫ m = y ≫ m') : m = m' := by
  refine (H (fun y => y ≫ m) fun y => ?_).unique (fun _ => rfl) (fun y => (h y).symm)
  obtain ⟨_, ⟨D, hD, rfl⟩, hy, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((y ≫ m).left (default : PrimeSpectrum ℂ))) isOpen_univ
  refine ⟨m.left ⁻¹ᵁ D, D, ?_, hD, fun y' hy' => ?_, fun φ => ⟨(m.left.app D).hom φ, fun y' _ => ?_⟩⟩
  · exact (top_le_preimage_comp y.left m.left D).1 ((top_le_preimage_iff_mem _ D).2 hy)
  · exact (top_le_preimage_comp y'.left m.left D).2 hy'
  · exact valAt'_comp y'.left m.left D φ

end TorusEnd


open TorusEnd in
theorem exists_isMonHom_of_map_periodLattice :
    (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f'
        : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶
        X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X Y
        : Over (Sp ℂ)), IsReduced Y.left → LocallyOfFiniteType Y.hom → ∀ F : (𝟙_ (Over (Sp ℂ)) ⟶
        Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D
        : X.left.Opens), ⊤ ≤ (y).left ⁻¹ᵁ U ∧ IsAffineOpen D ∧ (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶
        Y), ⊤ ≤ (y').left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧ ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left,
        U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → valAt' y'.left U ρ = valAt' (F
        y').left D φ) → ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y) → (∀ (X Y : Over (Sp
        ℂ)), IsReduced X.left → IsReduced Y.left → LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom → IsReduced (X
        ⊗ Y).left) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ (N : ℕ) (F
        : (Fin g → ℂ) →ₗ[ℂ] (Fin g →
        ℂ)), (∀ l ∈ periodLattice τ, F l ∈ periodLattice τ) → ∃ d : ℕ, ∀ z₀, ∃ G : (Fin g →
        ℂ) → ℂ, G z₀ ≠ 0 ∧ ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z
        + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 +
        ofIntVec n ⬝ᵥ z)) * f z) → (Differentiable ℂ (fun z => f (F z) * G z) ∧ ∀ (n n'
        : Fin g → ℤ) z, (fun z => f (F z) * G z) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d
        : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => f (F
        z) * G z) z)) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
        g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c
        i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n'
        : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) /
        2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N
        : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z
        : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp
        ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin
        N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
        (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left,
        U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex
        w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ
        : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D
        c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i
        : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D
        c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ)
        • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin
        N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso
        (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g →
        ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠
        0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → ∀ [GrpObj X], (∀ z w, ex (z +
        w) = ex z * ex w) → ∀ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g →
        ℂ), (∀ l ∈ periodLattice τ, F l ∈ periodLattice τ) → ∃ f : X ⟶ X, IsMonHom f ∧ ∀ z, ex (F
        z) = ex z ≫ f) := by
  intro _ Hm Hred HG Hθ g τ hτ N hN X ex D ⟨hint, hprop, hsurj, hex, _, hD, hcov⟩ hreg _ hadd F hF
  have hXr : IsReduced X.left := inferInstance
  have hXf : LocallyOfFiniteType X.hom := inferInstance
  let Φ : (𝟙_ (Over (Sp ℂ)) ⟶ X) → (𝟙_ (Over (Sp ℂ)) ⟶ X) := fun y => ex (F (Function.surjInv hsurj y))
  have hΦ : ∀ z, Φ (ex z) = ex (F z) := fun z => by
    refine (hex _ _).2 ?_
    rw [← map_sub]
    exact hF _ ((hex _ _).1 (Function.surjInv_eq hsurj _))
  obtain ⟨d, hd⟩ := HG g τ hτ N F hF
  have hθ := (Hθ g τ hτ N (by omega)).1
  obtain ⟨f, hf, -⟩ := Hm X X hXr hXf Φ fun y => by
    obtain ⟨z₀, rfl⟩ := hsurj y
    obtain ⟨c, hc⟩ := exists_top_le_preimage_of_iSup_eq_top (ex (F z₀)).left D hcov
    obtain ⟨haff, -, hmem, r, hr, hgen⟩ := hD c
    obtain ⟨G, hG0, hG⟩ := hd z₀
    choose U φ hU using fun c' => hreg d _ _ (hG _ (hθ c')) (hG _ (hθ c))
    have hle : ∀ c', Finset.univ.inf U ≤ U c' := fun c' => Finset.inf_le (Finset.mem_univ c')
    refine ⟨Finset.univ.inf U, D c, ?_, haff, fun y' hy' => ?_, fun ψ => ?_⟩
    · exact (top_le_preimage_finset_inf _ _ _).2 fun c' _ =>
        (hU c' z₀).1.2 (mul_ne_zero ((hmem _).1 hc) hG0)
    · obtain ⟨z, rfl⟩ := hsurj y'
      rw [hΦ]
      exact (hmem _).2 (left_ne_zero_of_mul ((hU c z).1.1 (top_le_preimage_mono _ (hle c) hy')))
    · obtain ⟨P, rfl⟩ := hgen ψ
      refine ⟨MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (fun c' => resG X.left (hle c') (φ c')) P, fun y' hy' => ?_⟩
      obtain ⟨z, rfl⟩ := hsurj y'
      have hq := (hU c z).1.1 (top_le_preimage_mono _ (hle c) hy')
      have h1 := left_ne_zero_of_mul hq
      have h2 := right_ne_zero_of_mul hq
      rw [hΦ, valAt'_eval₂ _ _ hy', valAt'_eval₂ _ _ ((hmem _).2 h1)]
      congr 2
      funext c'
      rw [valAt'_res _ _ _ hy', (hU c' z).2 hq, hr c' _ h1, mul_div_mul_right _ _ h2]
  have hfe : ∀ z, ex (F z) = ex z ≫ f := fun z => by rw [hf, hΦ]
  have h0 : ex 0 = η[X] := by
    have h := hadd 0 0
    rw [add_zero] at h
    have h1 : ex 0 = 1 := by simpa using h
    rw [h1, Hom.one_def, toUnit_unit, Category.id_comp]
  refine ⟨f, ⟨?_, ?_⟩, hfe⟩
  · rw [← h0, ← hfe, map_zero]
  · have hft : LocallyOfFiniteType (X ⊗ X).hom := by
      change LocallyOfFiniteType (pullback.fst X.hom X.hom ≫ X.hom)
      infer_instance
    refine hom_ext_of_points (Hm X (X ⊗ X) (Hred X X hXr hXr hXf hXf) hft) fun y => ?_
    obtain ⟨z, hz⟩ := hsurj (y ≫ fst X X)
    obtain ⟨w, hw⟩ := hsurj (y ≫ snd X X)
    have hy : y = lift (ex z) (ex w) := by
      ext1 <;> simp [hz, hw]
    rw [hy, ← Category.assoc, ← Hom.mul_def, ← hadd, ← hfe, map_add (f := _), hadd, Hom.mul_def, ← Category.assoc, lift_map,
      ← hfe, ← hfe]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniqueHomOfLocallyRegular
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace PointwiseRegular

theorem hom_ext {X Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced Y] {f g : Y ⟶ X}
    (h : ∀ y : Sp ℂ ⟶ Y, y ≫ p = 𝟙 _ → y ≫ f = y ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall _ _ fun z => ?_
  obtain ⟨_, ⟨D, hD, rfl⟩, hz, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f z)) isOpen_univ
  have hle : f ⁻¹ᵁ D ≤ g ⁻¹ᵁ D := ComplexPoints.opens_le_of_complexPoints p _ _ fun y hy hyD => by
    rw [← top_le_preimage_comp] at hyD ⊢
    rwa [← h y hy]
  refine ⟨f ⁻¹ᵁ D, hz, ?_⟩
  have : IsAffine (Scheme.Opens.toScheme (X := X) D) := hD
  have key : f.resLE D (f ⁻¹ᵁ D) le_rfl = g.resLE D (f ⁻¹ᵁ D) hle := by
    refine ComplexPoints.hom_ext_of_points ((f ⁻¹ᵁ D).ι ≫ p) (terminal.from _) (terminal.hom_ext _ _) fun x hx => ?_
    rw [← cancel_mono (Scheme.Opens.ι (X := X) D), Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, ← Category.assoc]
    exact h _ (by rw [Category.assoc]; exact hx)
  rw [← Scheme.Hom.resLE_comp_ι f le_rfl, key, Scheme.Hom.resLE_comp_ι]

def ofRingHom {X Y : Scheme.{0}} (U : Y.Opens) {D : X.Opens} (hD : IsAffineOpen D) (r : Γ(X, D) →+* Γ(Y, U)) :
    U.toScheme ⟶ X :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom r) ≫ hD.fromSpec

theorem top_le_preimage_ι {Y : Scheme.{0}} (U : Y.Opens) (y : Sp ℂ ⟶ U.toScheme) : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U := by
  rw [top_le_preimage_comp]
  simp

theorem comp_ofRingHom {X Y : Scheme.{0}} (U : Y.Opens) {D : X.Opens} (hD : IsAffineOpen D)
    (r : Γ(X, D) →+* Γ(Y, U)) (y : Sp ℂ ⟶ U.toScheme) (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ D)
    (h : ∀ φ, valAt' (y ≫ U.ι) U (r φ) = valAt' x D φ) : y ≫ ofRingHom U hD r = x := by
  have hy := top_le_preimage_ι U y
  have e1 : CommRingCat.ofHom r ≫ (y ≫ U.ι).appLE U ⊤ hy = x.appLE D ⊤ hx := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]
    ext φ
    have := h φ
    rw [valAt'_eq_valAt _ hy, valAt'_eq_valAt _ hx] at this
    exact this
  have e2 : (isAffineOpen_top (Sp ℂ)).fromSpec ≫ y ≫ U.toSpecΓ = Spec.map ((y ≫ U.ι).appLE U ⊤ hy) := by
    rw [IsAffineOpen.fromSpec_top, Iso.inv_comp_eq, Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc,
      ← Spec.map_comp]
    congr 2
    rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  have : IsIso (isAffineOpen_top (Sp ℂ)).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← cancel_epi (isAffineOpen_top (Sp ℂ)).fromSpec, ← hD.SpecMap_appLE_fromSpec x _ hx, ← e1, ofRingHom,
    reassoc_of% e2, Spec.map_comp_assoc]

theorem exists_ringHom {X Y : Over (Sp ℂ)} [IsReduced Y.left] [LocallyOfFiniteType Y.hom]
    (F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : Y.left.Opens) (D : X.left.Opens)
    (hF : ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U → ⊤ ≤ (F y).left ⁻¹ᵁ D)
    (h : ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U ρ = valAt' (F y).left D φ) :
    ∃ r : Γ(X.left, D) →+* Γ(Y.left, U), ∀ φ, ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U (r φ) = valAt' (F y).left D φ := by
  choose r hr using h
  have ext : ∀ a b : Γ(Y.left, U), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U a = valAt' y.left U b) → a = b := fun a b hab =>
    ComplexPoints.eq_of_valAt'_eq Y.hom U a b fun x hx hU => hab (Over.homMk x hx) hU
  refine ⟨⟨⟨⟨r, ?_⟩, ?_⟩, ?_, ?_⟩, hr⟩
  · exact ext _ _ fun y hy => by
      rw [hr _ y hy]; exact (valAt'_one _ (hF y hy)).trans (valAt'_one _ hy).symm
  · exact fun a b => ext _ _ fun y hy => by
      refine (hr _ y hy).trans (((valAt'_mul _ _ _ _).trans ?_).trans (valAt'_mul _ _ _ _).symm)
      rw [hr _ y hy, hr _ y hy]
  · exact ext _ _ fun y hy => (hr _ y hy).trans ((valAt'_zero _ _).trans (valAt'_zero _ _).symm)
  · exact fun a b => ext _ _ fun y hy => by
      refine (hr _ y hy).trans (((valAt'_add _ _ _ _).trans ?_).trans (valAt'_add _ _ _ _).symm)
      exact congrArg₂ (· + ·) (hr _ y hy).symm (hr _ y hy).symm

theorem existsUnique_hom {X Y : Over (Sp ℂ)} [IsReduced Y.left] [LocallyOfFiniteType Y.hom]
    (F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (h : ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D : X.left.Opens), ⊤ ≤ y.left ⁻¹ᵁ U ∧ IsAffineOpen D ∧
      (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y'.left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧
      ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y'.left ⁻¹ᵁ U →
        valAt' y'.left U ρ = valAt' (F y').left D φ) :
    ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y := by
  choose U D hU hD hF hρ using h
  have loc : ∀ i, ∃ m : (U i).toScheme ⟶ X.left, ∀ (z : Sp ℂ ⟶ (U i).toScheme) (y : 𝟙_ (Over (Sp ℂ)) ⟶ Y),
      y.left = z ≫ (U i).ι → z ≫ m = (F y).left := fun i => by
    obtain ⟨r, hr⟩ := exists_ringHom F (U i) (D i) (hF i) (hρ i)
    refine ⟨ofRingHom (U i) (hD i) r, fun z y hy => ?_⟩
    have hyU : ⊤ ≤ y.left ⁻¹ᵁ U i := by rw [hy]; exact top_le_preimage_ι _ z
    refine comp_ofRingHom _ _ r z _ (hF i y hyU) fun φ => ?_
    rw [← hr φ y hyU, hy]
  choose m hm using loc
  have hcov : TopologicalSpace.IsOpenCover U :=
    ComplexPoints.iSup_eq_top_of_complexPoints Y.hom U fun x hx => ⟨Over.homMk x hx, hU _⟩
  let 𝒰 := Y.left.openCoverOfIsOpenCover U hcov
  have hc : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ m i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ m j := fun i j => by
    have : IsReduced (pullback (𝒰.f i) (𝒰.f j)) :=
      isReduced_of_isOpenImmersion (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
    refine hom_ext ((pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) ≫ Y.hom) fun z hz => ?_
    let y : 𝟙_ (Over (Sp ℂ)) ⟶ Y := Over.homMk (z ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
      ((Category.assoc _ _ _).trans hz)
    refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
    refine (hm i _ y (Category.assoc _ _ _).symm).trans (hm j _ y ?_).symm
    change z ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i = (z ≫ pullback.snd (𝒰.f i) (𝒰.f j)) ≫ 𝒰.f j
    rw [pullback.condition, Category.assoc]
  have hg : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ Y, y.left ≫ 𝒰.glueMorphisms m hc = (F y).left := fun y => by
    have hr : Set.range y.left ⊆ Set.range (U y).ι := by
      rintro _ ⟨a, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hU y (Set.mem_univ a)
    have e := IsOpenImmersion.lift_fac (U y).ι y.left hr
    have e2 : (U y).ι ≫ 𝒰.glueMorphisms m hc = m y := 𝒰.ι_glueMorphisms m hc y
    refine Eq.trans ?_ (hm y _ y e.symm)
    rw [← e2, ← Category.assoc, e]
  have hw : 𝒰.glueMorphisms m hc ≫ X.hom = Y.hom := by
    refine hom_ext Y.hom fun z hz => ?_
    have := hg (Over.homMk z hz)
    rw [hz, ← Category.assoc]
    exact (congrArg (· ≫ X.hom) this).trans (Over.w (F _))
  refine ⟨Over.homMk _ hw, fun y => Over.OverMorphism.ext (hg y), fun m' hm' => Over.OverMorphism.ext ?_⟩
  refine hom_ext Y.hom fun z hz => ?_
  exact (congrArg (fun φ => φ.left) (hm' (Over.homMk z hz))).trans (hg (Over.homMk z hz)).symm

end PointwiseRegular

theorem existsUnique_hom_of_locally_regular : (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X Y : Over (Sp ℂ)), IsReduced Y.left → LocallyOfFiniteType Y.hom → ∀ F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D : X.left.Opens), ⊤ ≤ (y).left ⁻¹ᵁ U ∧ IsAffineOpen D ∧ (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧ ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → valAt' y'.left U ρ = valAt' (F y').left D φ) → ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y) :=
  fun _ _ _ _ _ _ F h => PointwiseRegular.existsUnique_hom F h

end GlobalTheory
end
end

