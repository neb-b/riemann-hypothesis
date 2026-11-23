module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KaehlerPushoutSplit
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.KaehlerPushout

open KaehlerDifferential

theorem exists_retraction (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K B A R] :
    ∃ r : Ω[R⁄K] →ₗ[R] R ⊗[A] Ω[A⁄K],
      (∀ x, r (KaehlerDifferential.mapBaseChange K A R x) = x) ∧
      (∀ y, r (KaehlerDifferential.mapBaseChange K B R y) = 0) := by
  let e := KaehlerDifferential.tensorKaehlerEquiv K B A R
  refine ⟨e.symm.toLinearMap ∘ₗ KaehlerDifferential.map K B R R, ?_, ?_⟩
  · intro x
    have key : KaehlerDifferential.map K B R R (KaehlerDifferential.mapBaseChange K A R x) = e x := by
      induction x with
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul s w =>
        have hw : w ∈ Submodule.span A (Set.range (KaehlerDifferential.D K A)) := by
          rw [KaehlerDifferential.span_range_derivation]; trivial
        induction hw using Submodule.span_induction generalizing s with
        | mem w hw =>
          obtain ⟨a, rfl⟩ := hw
          simp [e, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
        | zero => simp
        | add u v _ _ hu hv => simp only [tmul_add, map_add (f := _), hu, hv]
        | smul a u _ hu =>
          rw [← TensorProduct.smul_tmul]
          exact hu _
    simp [key]
  · intro y
    induction y with
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
    | tmul s w =>
      have hw : w ∈ Submodule.span B (Set.range (KaehlerDifferential.D K B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hw using Submodule.span_induction generalizing s with
      | mem w hw =>
        obtain ⟨b, rfl⟩ := hw
        simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
      | zero => simp
      | add u v _ _ hu hv => simp only [tmul_add, map_add (f := _), hu, hv, add_zero]
      | smul b u _ hu =>
        rw [← TensorProduct.smul_tmul]
        exact hu _

theorem range_sup_range (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [h : Algebra.IsPushout K A B R] :
    LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔
      LinearMap.range (KaehlerDifferential.mapBaseChange K B R) = ⊤ := by
  set S := LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔
      LinearMap.range (KaehlerDifferential.mapBaseChange K B R) with hS
  have hA : ∀ a : A, KaehlerDifferential.D K R (algebraMap A R a) ∈ S := fun a =>
    Submodule.mem_sup_left ⟨1 ⊗ₜ KaehlerDifferential.D K A a, by
      simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]⟩
  have hB : ∀ b : B, KaehlerDifferential.D K R (algebraMap B R b) ∈ S := fun b =>
    Submodule.mem_sup_right ⟨1 ⊗ₜ KaehlerDifferential.D K B b, by
      simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]⟩
  have hD : ∀ r : R, KaehlerDifferential.D K R r ∈ S := by
    intro r
    induction r using h.out.inductionOn with
    | tmul b => exact hB b
    | smul a y hy =>
      rw [Algebra.smul_def, Derivation.leibniz]
      exact S.add_mem (S.smul_mem _ hy) (S.smul_mem _ (hA a))
    | add x y hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  exact hD r

theorem kaehler_pushout_split : ∀ (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R] [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R] [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K A B R], ∃ (r : Ω[R⁄K] →ₗ[R] R ⊗[A] Ω[A⁄K]) (π : Ω[R⁄K] →ₗ[R] R ⊗[B] Ω[B⁄K]), (∀ x, r (KaehlerDifferential.mapBaseChange K A R x) = x) ∧ (∀ y, r (KaehlerDifferential.mapBaseChange K B R y) = 0) ∧ (∀ x, π (KaehlerDifferential.mapBaseChange K A R x) = 0) ∧ (∀ y, π (KaehlerDifferential.mapBaseChange K B R y) = y) ∧ LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔ LinearMap.range (KaehlerDifferential.mapBaseChange K B R) = ⊤ := by
  intro K A B R _ _ _ _ _ _ _ _ _ _ _ h
  haveI hs : Algebra.IsPushout K B A R := h.symm
  obtain ⟨r, hr₁, hr₂⟩ := exists_retraction K A B R
  obtain ⟨π, hπ₁, hπ₂⟩ := exists_retraction K B A R
  exact ⟨r, π, hr₁, hr₂, hπ₂, hπ₁, range_sup_range K A B R⟩

end GlobalTheory.CompanionTheory.KaehlerPushout
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelBaseChangeTowerEquiv
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.PerfectFirstCohomology

theorem ker_baseChange_tower (R A K Q P : Type) [CommRing R] [CommRing A] [CommRing K] [Algebra R A]
    [Algebra A K] [Algebra R K] [IsScalarTower R A K] [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P) :
    Nonempty (LinearMap.ker ((d.baseChange A).baseChange K) ≃ₗ[K] LinearMap.ker (d.baseChange K)) := by
  let e₁ := AlgebraTensorModule.cancelBaseChange R A K K Q
  let e₂ := AlgebraTensorModule.cancelBaseChange R A K K P
  have comm : ∀ x, e₂ (((d.baseChange A).baseChange K) x) = (d.baseChange K) (e₁ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul k y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [tmul_add, map_add (f := _), hx, hy]
      | tmul a q =>
        simp [e₁, e₂, LinearMap.baseChange_tmul, TensorProduct.smul_tmul']
  refine ⟨LinearEquiv.ofSubmodules e₁ _ _ ?_⟩
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := comm x
    rw [hx, map_zero] at this
    exact this.symm
  · intro hy
    refine ⟨e₁.symm y, ?_, by simp⟩
    apply e₂.injective
    rw [comm, map_zero]
    simpa using hy

end GlobalTheory.CompanionTheory.PerfectFirstCohomology
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFreeAtPrimesOfConstantRank
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.KerLocal

theorem ker_baseChange_localization_free :
    ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P]
      (d : Q →ₗ[R] P) (g : ℕ), Module.Finite R (LinearMap.ker d) →
      Module.Projective R (LinearMap.ker d) →
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.ker d) p = g) →
      ∀ (p : Ideal R) [p.IsPrime],
        Module.Free (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧
        Module.Finite (Localization.AtPrime p)
          (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧
        Module.finrank (Localization.AtPrime p)
          (LinearMap.ker (d.baseChange (Localization.AtPrime p))) = g := by
  intro R Q P _ _ _ _ _ d g hfin hproj hrk p _
  have hflat : Module.Flat R (Localization.AtPrime p) :=
    IsLocalization.flat (Localization.AtPrime p) p.primeCompl
  let e1 : Localization.AtPrime p ⊗[R] LinearMap.ker d ≃ₗ[Localization.AtPrime p]
      LinearMap.ker (d.baseChange (Localization.AtPrime p)) :=
    LinearMap.tensorKerEquiv (Localization.AtPrime p) (Localization.AtPrime p) d
  let e2 : Localization.AtPrime p ⊗[R] LinearMap.ker d ≃ₗ[Localization.AtPrime p]
      LocalizedModule p.primeCompl (LinearMap.ker d) :=
    (IsLocalizedModule.isBaseChange p.primeCompl (Localization.AtPrime p)
      (LocalizedModule.mkLinearMap p.primeCompl (LinearMap.ker d))).equiv
  have hfree : Module.Free (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] LinearMap.ker d) := Module.free_of_flat_of_isLocalRing
  refine ⟨Module.Free.of_equiv e1, Module.Finite.equiv e1, ?_⟩
  rw [← e1.finrank_eq, e2.finrank_eq]
  exact hrk ⟨p, inferInstance⟩

end GlobalTheory.CompanionTheory.KerLocal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeAnnihilatorWithinNhds
section
open Matrix ValuativeRel
open scoped Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.AnnihShrink

theorem exists_ne_zero_valuation_lt (k : Type) [Field k] [ValuativeRel k] [ValuativeRel.IsNontrivial k]
    (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) : ∃ t : k, t ≠ 0 ∧ valuation k t < γ := by
  obtain ⟨γ₀, h0, h1⟩ := ValuativeRel.IsNontrivial.condition (R := k)
  obtain ⟨ε, hε0, hε1⟩ : ∃ ε : ValueGroupWithZero k, ε ≠ 0 ∧ ε < 1 := by
    rcases lt_or_gt_of_ne h1 with h | h
    · exact ⟨γ₀, h0, h⟩
    · exact ⟨γ₀⁻¹, inv_ne_zero h0, inv_lt_one_of_one_lt₀ h⟩
  obtain ⟨t, ht⟩ := valuation_surjective (K := k) (ε * γ)
  have hpos : 0 < γ := zero_lt_iff.mpr hγ
  refine ⟨t, ?_, ?_⟩
  · rw [← (valuation k).ne_zero_iff, ht]
    exact mul_ne_zero hε0 hγ
  · rw [ht]
    exact mul_lt_of_lt_one_left hpos hε1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (n : ℕ) (b : k) : AddSubgroup (Fin n → k) where
  carrier := {a | ∀ j, valuation k (a j) ≤ valuation k b}
  zero_mem' := fun j => by simp
  add_mem' := fun {x y} hx hy j =>
    ((valuation k).map_add _ _).trans (max_le (hx j) (hy j))
  neg_mem' := fun {x} hx j => by simpa using hx j

theorem isCompact_box (n : ℕ) (b : k) : IsCompact (box n b : Set (Fin n → k)) := by
  have : (box n b : Set (Fin n → k)) =
      Set.univ.pi (fun _ => {y : k | valuation k y ≤ valuation k b}) := by
    ext a
    exact ⟨fun h j _ => h j, fun h j => h j (Set.mem_univ j)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _

theorem isOpen_box (n : ℕ) (b : k) (hb : b ≠ 0) : IsOpen (box n b : Set (Fin n → k)) := by
  have hvb : valuation k b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  have hU : Set.univ.pi (fun _ : Fin n => {y : k | valuation k y < valuation k b}) ∈
      nhds (0 : Fin n → k) :=
    set_pi_mem_nhds Set.finite_univ fun j _ =>
      (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hvb
  refine (box n b).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset hU ?_)
  intro x hx j
  exact (hx j (Set.mem_univ j)).le

theorem exists_compact_open_annihilator_subset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (U : Set (Fin n → k)),
      U ∈ nhds (0 : Fin n → k) → ∃ A : AddSubgroup (Fin n → k),
        IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧
        {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ⊆ U := by
  intro k _ _ _ _ ψ _ hne n U hU
  obtain ⟨y₀, hy⟩ : ∃ y : k, ψ y ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne (AddChar.ext _ _ fun t => by simpa using hall t)
  have hy0 : y₀ ≠ 0 := by
    rintro rfl
    exact hy (by simp)

  obtain ⟨I, V, hV, hIV⟩ : ∃ (I : Set (Fin n)) (V : Fin n → Set k),
      (∀ i, V i ∈ nhds (0 : k)) ∧ I.pi V ⊆ U := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, _, V, hV, hIV⟩ := hU
    exact ⟨I, V, hV, hIV⟩
  have hball : ∀ i, ∃ γ : (ValueGroupWithZero k)ˣ, {y : k | valuation k y < γ} ⊆ V i := fun i =>
    (IsValuativeTopology.mem_nhds_zero_iff (V i)).1 (hV i)
  choose g hg using hball
  obtain ⟨γ, hγ0, hγ⟩ : ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ i, γ ≤ (g i : ValueGroupWithZero k) := by
    obtain ⟨m, hm⟩ := Finite.exists_ge g
    exact ⟨m, m.ne_zero, fun i => Units.val_le_val.2 (hm i)⟩
  obtain ⟨t, ht0, ht⟩ := exists_ne_zero_valuation_lt k γ hγ0
  refine ⟨box n (y₀ / t), isCompact_box n _, isOpen_box n _ (div_ne_zero hy0 ht0), ?_⟩
  intro ξ hξ
  apply hIV
  intro i _
  apply hg i
  show valuation k (ξ i) < g i
  refine lt_of_lt_of_le ?_ (hγ i)
  by_contra hlt
  have hle : γ ≤ valuation k (ξ i) := not_lt.mp hlt
  have hvξ : valuation k (ξ i) ≠ 0 := (lt_of_lt_of_le (zero_lt_iff.mpr hγ0) hle).ne'
  have hξi : ξ i ≠ 0 := (Valuation.ne_zero_iff _).1 hvξ
  have hmem : (Pi.single i (y₀ / ξ i) : Fin n → k) ∈ box n (y₀ / t) := by
    intro j
    by_cases h : j = i
    · subst h
      have he : y₀ / ξ j = (y₀ / t) * (t / ξ j) := by field_simp
      rw [Pi.single_eq_same, he, map_mul]
      refine mul_le_of_le_one_right' ?_
      rw [map_div₀]
      exact (div_le_one₀ (zero_lt_iff.mpr hvξ)).2 (ht.le.trans hle)
    · simp [Pi.single_eq_of_ne h]
  have h1 := hξ _ hmem
  rw [dotProduct_single, mul_div_cancel₀ _ hξi] at h1
  exact hy h1

end GlobalTheory.CompanionTheory.AnnihShrink
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeOneOfPowerBounds
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.Casselman

theorem le_one_of_forall_sqrt_mul_rpow_lt :
    ∀ (δ r : ℝ), 0 < δ → δ < 1 → 0 ≤ r →
      (∀ ε : ℝ, 0 < ε → δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) < 1) → r ≤ 1 := by
  intro δ r hδ hδ1 hr h
  by_contra hlt
  rw [not_le] at hlt
  have hx : 0 < Real.sqrt δ * r := mul_pos (Real.sqrt_pos.mpr hδ) (by linarith)
  have hcont : ContinuousAt (fun ε : ℝ => δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε)) 0 := by
    apply ContinuousAt.mul continuousAt_const
    exact (Real.continuousAt_const_rpow hx.ne').comp
      (continuous_const.add continuous_id).continuousAt
  have h0 : δ⁻¹ * (Real.sqrt δ * r) ^ ((2 : ℝ) + 0) = r ^ 2 := by
    rw [add_zero, Real.rpow_two, mul_pow, Real.sq_sqrt hδ.le, inv_mul_cancel_left₀ hδ.ne']
  have h1 : (1 : ℝ) < δ⁻¹ * (Real.sqrt δ * r) ^ ((2 : ℝ) + 0) := by
    rw [h0]
    nlinarith
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 1 < δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) :=
    hcont.eventually (lt_mem_nhds h1)
  obtain ⟨ε, hε1, hε0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[Set.Ioi (0 : ℝ)] 0, x ∈ Set.Ioi (0 : ℝ))).exists
  exact lt_asymm (h ε hε0) hε1

end GlobalTheory.CompanionTheory.Casselman
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraFunctionCalculus
section
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.AdProj

noncomputable def entryMul {n : ℕ} (h : Fin n → ℝ) (g : ℝ → ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (g (h i - h j) : ℂ) * X i j

theorem diagonal_commutator {n : ℕ} (h : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.diagonal (fun i => (h i : ℂ)) * X - X * Matrix.diagonal (fun i => (h i : ℂ))
      = entryMul h (fun t => t) X := by
  ext i j
  simp only [entryMul, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  push_cast
  ring

theorem entryMul_pow_mem {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hD : Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤)
    (hbr : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ 𝔤) (k : ℕ) :
    entryMul h (fun t => t ^ k) X ∈ 𝔤 := by
  induction k with
  | zero =>
    have h0 : entryMul h (fun t => t ^ 0) X = X := by
      ext i j
      simp [entryMul]
    rw [h0]
    exact hX
  | succ k ih =>
    have hs : entryMul h (fun t => t ^ (k + 1)) X =
        Matrix.diagonal (fun i => (h i : ℂ)) * entryMul h (fun t => t ^ k) X -
          entryMul h (fun t => t ^ k) X * Matrix.diagonal (fun i => (h i : ℂ)) := by
      rw [diagonal_commutator]
      ext i j
      simp only [entryMul, Matrix.of_apply]
      push_cast
      ring
    rw [hs]
    exact hbr _ hD _ ih

theorem entryMul_poly_mem {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hD : Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤)
    (hbr : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ 𝔤) (p : Polynomial ℝ) :
    entryMul h (fun t => p.eval t) X ∈ 𝔤 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hs : entryMul h (fun t => (p + q).eval t) X =
        entryMul h (fun t => p.eval t) X + entryMul h (fun t => q.eval t) X := by
      ext i j
      simp only [entryMul, Matrix.of_apply, Matrix.add_apply, Polynomial.eval_add]
      push_cast
      ring
    rw [hs]
    exact 𝔤.add_mem hp hq
  | monomial m a =>
    have hs : entryMul h (fun t => (Polynomial.monomial m a).eval t) X =
        a • entryMul h (fun t => t ^ m) X := by
      ext i j
      simp only [entryMul, Matrix.of_apply, Matrix.smul_apply, Polynomial.eval_monomial,
        Complex.real_smul]
      push_cast
      ring
    rw [hs]
    exact 𝔤.smul_mem a (entryMul_pow_mem 𝔤 h hD hbr hX m)

theorem mem_of_entrywise {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ) :
    Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤 → (∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) →
      ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤 := by
  intro hD hbr f X hX
  obtain ⟨S, hS⟩ : ∃ S : Finset ℝ, ∀ i j, h i - h j ∈ S :=
    ⟨Finset.univ.image (fun q : Fin n × Fin n => h q.1 - h q.2),
      fun i j => Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩
  have key : ∀ x ∈ S, (Lagrange.interpolate S id f).eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (s := S) (r := f) Function.injective_id.injOn hx
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℝ, ∀ i j, p.eval (h i - h j) = f (h i - h j) :=
    ⟨Lagrange.interpolate S id f, fun i j => key _ (hS i j)⟩
  have heq : (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) = entryMul h (fun t => p.eval t) X := by
    ext i j
    simp only [entryMul, Matrix.of_apply, hp]
  rw [heq]
  exact entryMul_poly_mem 𝔤 h hD hbr hX p

end GlobalTheory.CompanionTheory.AdProj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraStarClosedBracket
section
open Matrix

namespace GlobalTheory.CompanionTheory.UnitaryBlock

theorem block_diagonal_of_keeps_frame : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ)
    (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Rᴴ * R = 1 →
    J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 →
    ∀ (g : Matrix (Fin n) (Fin n) ℂ) (h : Matrix (Fin D) (Fin D) ℂ), gᴴ * J * g = J →
    g * C = C * h → gᴴ * C = C * hᴴ →
    IsUnit h ∧ g * (J * C) = (J * C) * (hᴴ)⁻¹ ∧ g * R = R * (Rᴴ * g * R) ∧
      (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R) = J' := by
  intro n D m J J' C R hJJ hJh hC hR hJR hCR hsum g h hg hgC hgHC
  have hl : (J * gᴴ * J) * g = 1 := by
    calc (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, hJJ]
  have hr : g * (J * gᴴ * J) = 1 := mul_eq_one_comm.mp hl
  have hgJ : g * J * gᴴ = J := by
    calc g * J * gᴴ = g * (J * gᴴ * J) * J := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = J := by rw [hr, Matrix.one_mul]

  obtain ⟨k, hkdef⟩ : ∃ k, k = Cᴴ * (J * gᴴ * J) * C := ⟨_, rfl⟩
  have hk : k * h = 1 := by
    calc k * h = Cᴴ * (J * gᴴ * J) * (C * h) := by
          rw [hkdef]; simp only [Matrix.mul_assoc]
      _ = Cᴴ * ((J * gᴴ * J) * g) * C := by
          rw [← hgC]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hl, Matrix.mul_one, hC]
  have hk' : h * k = 1 := mul_eq_one_comm.mp hk
  have hunit : IsUnit h := ⟨⟨h, k, hk', hk⟩, rfl⟩
  have hdet : IsUnit hᴴ.det := by
    have : IsUnit hᴴ := by
      refine ⟨⟨hᴴ, kᴴ, ?_, ?_⟩, rfl⟩
      · rw [← Matrix.conjTranspose_mul, hk, Matrix.conjTranspose_one]
      · rw [← Matrix.conjTranspose_mul, hk', Matrix.conjTranspose_one]
    exact (Matrix.isUnit_iff_isUnit_det _).mp this
  have hJC : g * (J * C) * hᴴ = J * C := by
    calc g * (J * C) * hᴴ = g * J * (C * hᴴ) := by simp only [Matrix.mul_assoc]
      _ = g * J * gᴴ * C := by rw [← hgHC]; simp only [Matrix.mul_assoc]
      _ = J * C := by rw [hgJ]
  have hsecond : g * (J * C) = (J * C) * (hᴴ)⁻¹ := by
    calc g * (J * C) = g * (J * C) * (hᴴ * (hᴴ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = (g * (J * C) * hᴴ) * (hᴴ)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (J * C) * (hᴴ)⁻¹ := by rw [hJC]

  have hgpC : (J * gᴴ * J) * C = C * k := by
    calc (J * gᴴ * J) * C = (J * gᴴ * J) * C * (h * k) := by rw [hk', Matrix.mul_one]
      _ = (J * gᴴ * J) * (C * h) * k := by simp only [Matrix.mul_assoc]
      _ = ((J * gᴴ * J) * g) * C * k := by rw [← hgC]; simp only [Matrix.mul_assoc]
      _ = C * k := by rw [hl, Matrix.one_mul]
  have hCgR : Cᴴ * (g * R) = 0 := by
    have hadj : Cᴴ * g = h * Cᴴ := by
      have := congrArg Matrix.conjTranspose hgHC
      simpa [Matrix.conjTranspose_mul] using this
    calc Cᴴ * (g * R) = (Cᴴ * g) * R := by simp only [Matrix.mul_assoc]
      _ = h * (Cᴴ * R) := by rw [hadj, Matrix.mul_assoc]
      _ = 0 := by rw [hCR, Matrix.mul_zero]
  have hgHJC : gᴴ * J * C = J * C * k := by
    calc gᴴ * J * C = (J * J) * (gᴴ * J * C) := by rw [hJJ, Matrix.one_mul]
      _ = J * ((J * gᴴ * J) * C) := by simp only [Matrix.mul_assoc]
      _ = J * C * k := by rw [hgpC, Matrix.mul_assoc]
  have hCJg : Cᴴ * J * g = kᴴ * Cᴴ * J := by
    have := congrArg Matrix.conjTranspose hgHJC
    simpa [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hCJgR : Cᴴ * J * (g * R) = 0 := by
    calc Cᴴ * J * (g * R) = (Cᴴ * J * g) * R := by simp only [Matrix.mul_assoc]
      _ = kᴴ * Cᴴ * (J * R) := by rw [hCJg]; simp only [Matrix.mul_assoc]
      _ = kᴴ * (Cᴴ * R) * J' := by rw [hJR]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hCR, Matrix.mul_zero, Matrix.zero_mul]
  have hthird : g * R = R * (Rᴴ * g * R) := by
    calc g * R = (C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ) * (g * R) := by rw [hsum, Matrix.one_mul]
      _ = C * (Cᴴ * (g * R)) + J * C * (Cᴴ * J * (g * R)) + R * (Rᴴ * g * R) := by
          simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = R * (Rᴴ * g * R) := by rw [hCgR, hCJgR]; simp
  refine ⟨hunit, hsecond, hthird, ?_⟩
  have hRJ : R * J' = J * R := hJR.symm
  have hRhJR : Rᴴ * J * R = J' := by
    calc Rᴴ * J * R = Rᴴ * (J * R) := by rw [Matrix.mul_assoc]
      _ = Rᴴ * R * J' := by rw [hJR, Matrix.mul_assoc]
      _ = J' := by rw [hR, Matrix.one_mul]
  calc (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R)
      = Rᴴ * gᴴ * (R * J') * (Rᴴ * g * R) := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = Rᴴ * gᴴ * J * (R * (Rᴴ * g * R)) := by rw [hRJ]; simp only [Matrix.mul_assoc]
    _ = Rᴴ * (gᴴ * J * g) * R := by rw [← hthird]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hg, hRhJR]

end GlobalTheory.CompanionTheory.UnitaryBlock
end

