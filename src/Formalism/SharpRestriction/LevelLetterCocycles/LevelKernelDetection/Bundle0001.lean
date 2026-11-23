module

public import Mathlib

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.CvZeroTerm
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf.ConvolutionAlt

open PowerSeries

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

def cv (f : PowerSeries R) (g : ℤ → M) (k : ℤ) : M := ∑ᶠ j : ℕ, coeff j f • g (k - j)

theorem cv_eq_sum (f : PowerSeries R) (g : ℤ → M) (m : ℤ) (hg : ∀ k < m, g k = 0) (k : ℤ) (N : ℕ)
    (hN : k - m < N) : cv f g k = ∑ j ∈ Finset.range N, coeff j f • g (k - j) := by
  unfold cv
  apply finsum_eq_sum_of_support_subset
  intro j hj
  rw [Function.mem_support] at hj
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hjN
  exact hj (by rw [hg _ (by omega), smul_zero])

theorem cv_low (f : PowerSeries R) (g : ℤ → M) (m : ℤ) (hg : ∀ k < m, g k = 0) (k : ℤ) (hk : k < m) :
    cv f g k = 0 := by
  rw [cv_eq_sum f g m hg k 0 (by omega), Finset.sum_range_zero]

theorem cv_vanish (f : PowerSeries R) (g : ℤ → M) (hg : ∀ k < 0, g k = 0) (N : ℕ)
    (hf : (X : PowerSeries R) ^ N ∣ f) (k : ℤ) (hk : k < N) : cv f g k = 0 := by
  rw [cv_eq_sum f g 0 hg k N (by omega)]
  apply Finset.sum_eq_zero
  intro j hj
  rw [PowerSeries.X_pow_dvd_iff.mp hf j (Finset.mem_range.mp hj), zero_smul]

theorem cv_map {M' : Type} [AddCommGroup M'] [Module R M'] (L : M →ₗ[R] M') (f : PowerSeries R) (g : ℤ → M)
    (m : ℤ) (hg : ∀ k < m, g k = 0) (k : ℤ) : L (cv f g k) = cv f (fun k => L (g k)) k := by
  obtain ⟨N, hN⟩ := exists_nat_gt (k - m)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cv_eq_sum f g m hg k N hN,
    cv_eq_sum f (fun j => L (g j)) m (fun j hj => by rw [hg j hj, map_zero]) k N hN,
    map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]

theorem cv_mul (f f' : PowerSeries R) (g : ℤ → M) (m : ℤ) (hg : ∀ k < m, g k = 0) (k : ℤ) :
    cv (f * f') g k = cv f (cv f' g) k := by
  obtain ⟨N, hN⟩ := exists_nat_gt (k - m)
  have hc : ∀ j < m, cv f' g j = 0 := fun j hj => cv_low f' g m hg j hj
  rw [cv_eq_sum (f * f') g m hg k N hN, cv_eq_sum f (cv f' g) m hc k N hN]
  have inner : ∀ a ∈ Finset.range N, coeff a f • cv f' g (k - a) =
      ∑ b ∈ Finset.range (N - a), coeff a f • coeff b f' • g (k - a - b) := by
    intro a _
    rw [cv_eq_sum f' g m hg (k - a) N (by omega), Finset.smul_sum]
    symm
    apply Finset.sum_subset (fun x hx => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.sub_le N a)))
    intro b _ hb
    rw [Finset.mem_range] at hb
    rw [hg (k - a - b) (by omega), smul_zero, smul_zero]
  calc ∑ j ∈ Finset.range N, coeff j (f * f') • g (k - j)
      = ∑ j ∈ Finset.range N, ∑ a ∈ Finset.range (j + 1),
          coeff a f • coeff (j - a) f' • g (k - a - ((j - a : ℕ) : ℤ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [PowerSeries.coeff_mul, Finset.sum_smul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => (coeff a f * coeff b f') • g (k - j)) j]
        refine Finset.sum_congr rfl fun a ha => ?_
        have ha' := Finset.mem_range.mp ha
        rw [mul_smul, show k - (a : ℤ) - ((j - a : ℕ) : ℤ) = k - j by omega]
    _ = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range (N - a),
          coeff a f • coeff b f' • g (k - a - b) :=
        Finset.sum_range_diag_flip N (fun a b => coeff a f • coeff b f' • g (k - a - b))
    _ = ∑ a ∈ Finset.range N, coeff a f • cv f' g (k - a) :=
        (Finset.sum_congr rfl inner).symm

end Formalism.MainNotions.N.Ln03.Pf.ConvolutionAlt

namespace Formalism.MainNotions.N.Ln03.Pf.ConvolutionAlt

open PowerSeries

variable {R M : Type} [Field R] [AddCommGroup M] [Module R M]

theorem cv_twist (L : M →ₗ[R] M) (c : R) (hc : c ≠ 0) (f : PowerSeries R) (g : ℤ → M) (m : ℤ)
    (hg : ∀ k < m, g k = 0) (k : ℤ) :
    c ^ k • L (cv f g k) = cv (rescale c f) (fun k => c ^ k • L (g k)) k := by
  obtain ⟨N, hN⟩ := exists_nat_gt (k - m)
  have hL : ∀ j < m, c ^ j • L (g j) = 0 := fun j hj => by rw [hg j hj, map_zero, smul_zero]
  rw [cv_map L f g m hg k,
    cv_eq_sum f (fun j => L (g j)) m (fun j hj => by rw [hg j hj, map_zero]) k N hN,
    cv_eq_sum (rescale c f) (fun j => c ^ j • L (g j)) m hL k N hN, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PowerSeries.coeff_rescale, smul_smul, smul_smul]
  congr 1
  have hp : c ^ j * c ^ (k - (j : ℤ)) = c ^ k := by
    rw [← zpow_natCast, ← zpow_add₀ hc]
    congr 1
    ring
  rw [← hp]
  ring

end Formalism.MainNotions.N.Ln03.Pf.ConvolutionAlt
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.ExistsBasisOfSurjective
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Module

private theorem exists_linear_rightInverse_of_surjective {R : Type} [CommRing R] {m₁ m₂ : ℕ}
    (f : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R)) (hf : Function.Surjective f) :
    ∃ s : (Fin m₂ → R) →ₗ[R] (Fin m₁ → R), ∀ y, f (s y) = y := by
  refine ⟨(Pi.basisFun R (Fin m₂)).constr R (fun j => (hf (Pi.single j 1)).choose), ?_⟩
  have h : f ∘ₗ (Pi.basisFun R (Fin m₂)).constr R (fun j => (hf (Pi.single j 1)).choose)
      = LinearMap.id := by
    refine (Pi.basisFun R (Fin m₂)).ext fun j => ?_
    rw [LinearMap.comp_apply, Basis.constr_basis, LinearMap.id_apply, Pi.basisFun_apply]
    exact (hf (Pi.single j 1)).choose_spec
  intro y
  exact LinearMap.congr_fun h y

theorem exists_basis_of_surjective {R : Type} [CommRing R] [IsLocalRing R] {m₁ m₂ : ℕ}
    (f : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R)) (hf : Function.Surjective f) :
    ∃ B : Module.Basis (Fin m₂ ⊕ Fin (m₁ - m₂)) R (Fin m₁ → R),
      (∀ j, f (B (Sum.inl j)) = Pi.single j 1) ∧ ∀ j, f (B (Sum.inr j)) = 0 := by
  obtain ⟨s, hs⟩ := exists_linear_rightInverse_of_surjective f hf
  have hfk : ∀ k : LinearMap.ker f, f (k : Fin m₁ → R) = 0 := fun k => LinearMap.mem_ker.mp k.2
  let q : (Fin m₁ → R) →ₗ[R] (Fin m₁ → R) := LinearMap.id - s ∘ₗ f
  have hq : ∀ x, q x = x - s (f x) := fun x => by
    first
    | rfl
    | simp [q]
  have hmem : ∀ x, q x ∈ LinearMap.ker f := fun x => by
    rw [hq, LinearMap.mem_ker, map_sub, hs, sub_self]
  let r : (Fin m₁ → R) →ₗ[R] LinearMap.ker f := LinearMap.codRestrict (LinearMap.ker f) q hmem
  have hr : ∀ x, (r x : Fin m₁ → R) = x - s (f x) := fun x => by
    first
    | exact hq x
    | simp [r, hq]
  have hrk : ∀ k : LinearMap.ker f, r k = k := fun k => by
    apply Subtype.ext
    rw [hr, hfk k, map_zero, sub_zero]
  have hfg : ∀ p : (Fin m₂ → R) × LinearMap.ker f, f (s p.1 + (p.2 : Fin m₁ → R)) = p.1 :=
    fun p => by rw [map_add (f := _), hs, hfk, add_zero]
  let g : (Fin m₂ → R) × LinearMap.ker f →ₗ[R] (Fin m₁ → R) :=
    LinearMap.coprod s (LinearMap.ker f).subtype
  let h : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R) × LinearMap.ker f := LinearMap.prod f r
  have hg : ∀ p, g p = s p.1 + (p.2 : Fin m₁ → R) := fun p => by
    first
    | rfl
    | simp [g]
  have hh : ∀ x, h x = (f x, r x) := fun x => by
    first
    | rfl
    | simp [h]
  have h₁ : g ∘ₗ h = LinearMap.id := LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, hh, hg, LinearMap.id_apply]
    show s (f x) + (r x : Fin m₁ → R) = x
    rw [hr]
    abel
  have h₂ : h ∘ₗ g = LinearMap.id := LinearMap.ext fun p => by
    rw [LinearMap.comp_apply, hg, hh, LinearMap.id_apply, hfg p]
    refine Prod.ext rfl (Subtype.ext ?_)
    show (r (s p.1 + (p.2 : Fin m₁ → R)) : Fin m₁ → R) = p.2
    rw [hr, hfg p]
    abel
  let e : ((Fin m₂ → R) × LinearMap.ker f) ≃ₗ[R] (Fin m₁ → R) := LinearEquiv.ofLinear g h h₁ h₂
  have he : ∀ p, f (e p) = p.1 := fun p => by
    show f (g p) = p.1
    rw [hg, hfg p]
  have hproj : Module.Projective R (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype r (LinearMap.ext fun k => by
      rw [LinearMap.comp_apply, Submodule.subtype_apply, hrk, LinearMap.id_apply])
  have hfin : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_surjective r (fun k => ⟨k, hrk k⟩)
  have hfree : Module.Free R (LinearMap.ker f) := by
    first
    | exact Module.free_of_flat_of_isLocalRing
    | exact Module.free_of_projective_of_isLocalRing
    | infer_instance
  let bk := Module.Free.chooseBasis R (LinearMap.ker f)
  let bp := (Pi.basisFun R (Fin m₂)).prod bk
  let b := bp.map e
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R (LinearMap.ker f)) = m₁ - m₂ := by
    have h1 := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
    omega
  have hb : ∀ i, f (b i) = (bp i).1 := fun i => by
    rw [Basis.map_apply, he]
  refine ⟨b.reindex (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFinOfCardEq hcard)),
    fun j => ?_, fun j => ?_⟩
  · rw [Basis.reindex_apply, hb]
    first
    | simp [bp, Basis.prod_apply]
    | simp [bp]
  · rw [Basis.reindex_apply, hb]
    first
    | simp [bp, Basis.prod_apply]
    | simp [bp]

end Formalism.MainNotions.N.Ln03.Pf
end
end

