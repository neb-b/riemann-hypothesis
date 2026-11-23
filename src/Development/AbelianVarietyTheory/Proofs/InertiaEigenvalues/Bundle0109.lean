module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitNorm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticGaussIntegralStableOfDualLattice
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilQuad

theorem gaussInt_stable_of_dual : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → ∀ (t : A.K) (M D : AddSubgroup A.L), IsOpen (M : Set A.L) → IsCompact (M : Set A.L) → IsOpen (D : Set A.L) → IsCompact (D : Set A.L) → (∀ m ∈ M, A.psiK ψ (t * x * A.NL m) = 1) → (D : Set A.L) = {y : A.L | ∀ m ∈ M, A.kerL ψ (t * x) y m = 1} → IsStableGauss A ψ x μ t (gaussInt A ψ x μ t (D : Set A.L)) := by
  intro F E _ _ _ _ hU A ψ x μ hψ hμ t M D hMo hMc hDo hDc hN hD
  obtain ⟨⟨bas⟩, hinj, hNL, hTr, -⟩ := Et.quadratic_structure F E A
  haveI : Module.Finite A.K A.L := Module.Finite.of_basis bas
  haveI : Module.Finite F A.L := Module.Finite.trans A.K A.L
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hpsi : ∀ u v : A.K, A.psiK ψ (u + v) = A.psiK ψ u * A.psiK ψ v := by
    intro u v
    simp only [Et.psiK, map_add (f := _), AddChar.map_add_eq_mul]
  have hNadd : ∀ y m : A.L, A.NL (y + m) = A.NL y + Algebra.trace A.K A.L (star y * m) + A.NL m := by
    intro y m
    apply hinj
    simp only [map_add (f := _), hNL, hTr, star_add, star_mul, star_star]
    ring
  set g : A.L → ℂ := fun y => A.psiK ψ (t * x * A.NL y) with hg
  have hgadd : ∀ y m : A.L, g (y + m) = g y * A.kerL ψ (t * x) y m * A.psiK ψ (t * x * A.NL m) := by
    intro y m
    simp only [hg, Et.kerL, ← hpsi, hNadd]
    congr 1
    ring
  have hkadd : ∀ y y' m : A.L, A.kerL ψ (t * x) (y + y') m = A.kerL ψ (t * x) y m * A.kerL ψ (t * x) y' m := by
    intro y y' m
    simp only [Et.kerL, ← hpsi, star_add, add_mul, map_add (f := _), mul_add]
  have hmemD : ∀ y, y ∈ D ↔ ∀ m ∈ M, A.kerL ψ (t * x) y m = 1 := fun y => Set.ext_iff.1 hD y
  have hMD : M ≤ D := by
    intro m hm
    rw [hmemD]
    intro m' hm'
    have h := hgadd m m'
    have h1 : g (m + m') = 1 := hN _ (M.add_mem hm hm')
    have h2 : g m = 1 := hN _ hm
    rw [h1, h2, hN _ hm'] at h
    simpa using h.symm

  have hgc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro y
    have c1 : Continuous (fun m : A.L => Algebra.trace A.K A.L (star y * m)) :=
      IsModuleTopology.continuous_of_linearMap
        (((Algebra.trace A.K A.L).comp (LinearMap.mulLeft A.K (star y))).restrictScalars F)
    have c2 : Continuous (fun m : A.L => Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))) :=
      (IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)).comp (continuous_const.mul c1)
    have hU0 : {m : A.L | m ∈ M ∧ ‖Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))‖ ≤ 1} ∈ 𝓝 (0 : A.L) := by
      have hM : (M : Set A.L) ∈ 𝓝 (0 : A.L) := hMo.mem_nhds M.zero_mem
      have h0 : Metric.closedBall (0 : F) 1 ∈ 𝓝 (Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * (0 : A.L)))) := by
        simp only [mul_zero, map_zero]
        exact Metric.closedBall_mem_nhds 0 one_pos
      have hbound : {m : A.L | ‖Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))‖ ≤ 1} ∈ 𝓝 (0 : A.L) :=
        Filter.mem_of_superset ((c2.continuousAt (x := (0 : A.L))).preimage_mem_nhds h0)
        (fun m hm => (show ‖Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))‖ ≤ 1 by
          simpa [Metric.mem_closedBall, dist_zero_right] using hm))
      filter_upwards [hM, hbound] with m hmM hmBound
      exact ⟨hmM, hmBound⟩
    have hU1 := (continuous_sub_right y).continuousAt.preimage_mem_nhds (by rw [sub_self]; exact hU0)
    refine ContinuousAt.congr (f := fun _ => g y) continuousAt_const ?_
    filter_upwards [hU1] with z hz
    show g y = g z
    obtain ⟨hzM, hz1⟩ := hz
    have := hgadd y (z - y)
    rw [add_sub_cancel] at this
    rw [this, hN _ hzM, Et.kerL, Et.psiK, hψ.1 _ hz1]
    simp

  refine ⟨D, hDo, hDc, fun Λ hΛo hΛc hDΛ => ?_⟩
  have hmeas : ∀ S : Set A.L, IsOpen S → MeasurableSet S := fun S hS => hS.measurableSet
  have hint : IntegrableOn g (Λ : Set A.L) μ := hgc.continuousOn.integrableOn_compact' hΛc (hmeas _ hΛo)
  have hsplit : (Λ : Set A.L) = (D : Set A.L) ∪ ((Λ : Set A.L) \ (D : Set A.L)) :=
    (Set.union_diff_cancel (show (D : Set A.L) ⊆ Λ from hDΛ)).symm

  haveI : DiscreteTopology (A.L ⧸ D) := QuotientAddGroup.discreteTopology hDo
  have hmk : Continuous (QuotientAddGroup.mk : A.L → A.L ⧸ D) := continuous_quot_mk
  set S : A.L ⧸ D → Set A.L := fun q => ((Λ : Set A.L) \ (D : Set A.L)) ∩ QuotientAddGroup.mk ⁻¹' {q} with hS
  have hSo : ∀ q, MeasurableSet (S q) := fun q =>
    ((hmeas _ hΛo).diff (hmeas _ hDo)).inter (hmeas _ ((isOpen_discrete {q}).preimage hmk))
  have hzero : ∀ q, ∫ y in S q, g y ∂μ = 0 := by
    intro q
    by_cases hne : (S q).Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, Measure.restrict_empty, integral_zero_measure]
    obtain ⟨y₀, ⟨hy₀Λ, hy₀D⟩, hy₀q⟩ := hne
    have hy₀ : ¬ ∀ m ∈ M, A.kerL ψ (t * x) y₀ m = 1 := fun h => hy₀D ((hmemD y₀).2 h)
    push_neg at hy₀
    obtain ⟨m₀, hm₀, hc⟩ := hy₀
    have hm₀D : m₀ ∈ D := hMD hm₀
    have hshift : ∀ y ∈ S q, g (m₀ + y) = A.kerL ψ (t * x) y₀ m₀ * g y := by
      intro y hy
      obtain ⟨-, hyq⟩ := hy
      have hrel : -y₀ + y ∈ D := by
        rw [← QuotientAddGroup.eq]
        exact (hy₀q.trans hyq.symm)
      have h1 : A.kerL ψ (t * x) y m₀ = A.kerL ψ (t * x) y₀ m₀ := by
        have := hkadd y₀ (-y₀ + y) m₀
        rw [add_neg_cancel_left, (hmemD _).1 hrel m₀ hm₀, mul_one] at this
        exact this
      rw [add_comm, hgadd, h1, hN _ hm₀]
      ring
    have hpre : (fun y => m₀ + y) ⁻¹' (S q) = S q := by
      ext y
      simp only [hS, Set.mem_preimage, Set.mem_inter_iff, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
      have e1 : m₀ + y ∈ Λ ↔ y ∈ Λ := ⟨fun h => by simpa using Λ.sub_mem h (hDΛ hm₀D), fun h => Λ.add_mem (hDΛ hm₀D) h⟩
      have e2 : m₀ + y ∈ D ↔ y ∈ D := ⟨fun h => by simpa using D.sub_mem h hm₀D, fun h => D.add_mem hm₀D h⟩
      have e3 : (QuotientAddGroup.mk (m₀ + y) : A.L ⧸ D) = QuotientAddGroup.mk y := by
        rw [QuotientAddGroup.eq]
        simpa using D.neg_mem hm₀D
      rw [e1, e2, e3]
    have htr := (measurePreserving_add_left μ m₀).setIntegral_preimage_emb (measurableEmbedding_addLeft m₀) g (S q)
    rw [hpre] at htr
    have h2 : ∫ y in S q, g (m₀ + y) ∂μ = A.kerL ψ (t * x) y₀ m₀ * ∫ y in S q, g y ∂μ := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun (hSo q) (fun y hy => hshift y hy)
    rw [h2] at htr
    have h3 : (A.kerL ψ (t * x) y₀ m₀ - 1) * ∫ y in S q, g y ∂μ = 0 := by rw [sub_mul, htr]; ring
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc)
  have hfin : (QuotientAddGroup.mk '' (Λ : Set A.L) : Set (A.L ⧸ D)).Finite :=
    (hΛc.image hmk).finite_of_discrete
  have hunion : ((Λ : Set A.L) \ (D : Set A.L)) = ⋃ q ∈ hfin.toFinset, S q := by
    ext y
    simp only [hS, Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hy
      exact ⟨_, ⟨y, hy.1, rfl⟩, hy, rfl⟩
    · rintro ⟨_, _, hy, _⟩
      exact hy
  have hrest : ∫ y in (Λ : Set A.L) \ (D : Set A.L), g y ∂μ = 0 := by
    rw [hunion, integral_biUnion_finset]
    · exact Finset.sum_eq_zero (fun q _ => hzero q)
    · exact fun q _ => hSo q
    · intro q₁ _ q₂ _ hq
      refine Set.disjoint_left.2 ?_
      rintro y ⟨-, h1⟩ ⟨-, h2⟩
      exact hq ((Set.mem_singleton_iff.1 h1).symm.trans (Set.mem_singleton_iff.1 h2))
    · exact fun q _ => hint.mono_set (fun y hy => hy.1.1)
  show ∫ y in (Λ : Set A.L), g y ∂μ = ∫ y in (D : Set A.L), g y ∂μ
  rw [hsplit, setIntegral_union Set.disjoint_sdiff_right ((hmeas _ hΛo).diff (hmeas _ hDo))
    (hint.mono_set hDΛ) (hint.mono_set Set.diff_subset), hrest, add_zero]

end GlobalTheory.JR.WeilQuad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RhoProdFiniteAlgebraWithInvolution
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.RhoProd

theorem out_iff {G : Type} [Group G] (H : Subgroup G) (P : G → Prop)
    (hP : ∀ g h, h ∈ H → (P (g * h) ↔ P g)) (g : G) :
    P (Quotient.out (QuotientGroup.mk g : G ⧸ H)) ↔ P g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh]; exact hP g h h.2

theorem card_prod {G G₁ G₂ : Type} [Group G] [Group G₁] [Group G₂]
    (H : Subgroup G) (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) (e : G ≃* G₁ × G₂)
    (he : ∀ g, g ∈ H ↔ (e g).1 ∈ H₁ ∧ (e g).2 ∈ H₂)
    (P : G → Prop) (P₁ : G₁ → Prop) (P₂ : G₂ → Prop)
    (hP : ∀ g, P g ↔ P₁ (e g).1 ∧ P₂ (e g).2)
    (h₁ : ∀ g h, h ∈ H₁ → (P₁ (g * h) ↔ P₁ g)) (h₂ : ∀ g h, h ∈ H₂ → (P₂ (g * h) ↔ P₂ g)) :
    Nat.card {k : G ⧸ H // P (Quotient.out k)} =
      Nat.card {k : G₁ ⧸ H₁ // P₁ (Quotient.out k)} * Nat.card {k : G₂ ⧸ H₂ // P₂ (Quotient.out k)} := by
  let E : G ⧸ H ≃ (G₁ ⧸ H₁) × (G₂ ⧸ H₂) :=
    (Quotient.congr e.toEquiv (by
      intro a b
      show QuotientGroup.leftRel H a b ↔ (QuotientGroup.leftRel H₁).prod (QuotientGroup.leftRel H₂) (e a) (e b)
      rw [Setoid.prod_apply, QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, he]
      simp [map_mul, map_inv])).trans (Setoid.prodQuotientEquiv _ _).symm
  have hE : ∀ g : G, E (QuotientGroup.mk g) = (QuotientGroup.mk (e g).1, QuotientGroup.mk (e g).2) := by
    intro g; rfl
  have hPi : ∀ g h, h ∈ H → (P (g * h) ↔ P g) := by
    intro g h hh
    rw [hP, hP, map_mul, Prod.fst_mul, Prod.snd_mul]
    exact and_congr (h₁ _ _ ((he h).1 hh).1) (h₂ _ _ ((he h).1 hh).2)
  rw [← Nat.card_prod]
  refine Nat.card_congr ((E.subtypeEquiv ?_).trans (Equiv.subtypeProdEquivProd))
  intro k
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
  rw [hE, out_iff H₁ P₁ h₁, out_iff H₂ P₂ h₂, ← hP]
  exact out_iff H P hPi g

variable {K : UQ}

def torusEquiv (B₁ B₂ : InvAlg K) : (B₁.prod B₂).T ≃* B₁.T × B₂.T where
  toFun t := (⟨Units.map (RingHom.fst B₁.A B₂.A).toMonoidHom (show (B₁.A × B₂.A)ˣ from t.1),
      congrArg Prod.fst t.2⟩,
    ⟨Units.map (RingHom.snd B₁.A B₂.A).toMonoidHom (show (B₁.A × B₂.A)ˣ from t.1),
      congrArg Prod.snd t.2⟩)
  invFun s := ⟨show (B₁.A × B₂.A)ˣ from MulEquiv.prodUnits.symm ((s.1 : B₁.Aˣ), (s.2 : B₂.Aˣ)),
      Prod.ext s.1.2 s.2.2⟩
  left_inv t := by
    apply Subtype.ext; apply Units.ext; rfl
  right_inv s := by
    ext <;> rfl
  map_mul' a b := by
    ext <;> rfl

theorem inv_mul_int (B : InvAlg K) (w : B.A) (g h : B.T)
    (hh : h ∈ (intUnits K.O B.A).subgroupOf B.T) :
    IsIntegral K.O ((((g * h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) ↔
      IsIntegral K.O ((((g : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) := by
  rw [Subgroup.mem_subgroupOf] at hh
  obtain ⟨hi, hi'⟩ := hh
  have e1 : ((((g * h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) =
      ((((h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((((g : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w) := by
    simp [mul_inv_rev, Units.val_mul, mul_assoc]
  have e2 : ((((g : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) =
      (((h : B.T) : B.Aˣ) : B.A) * ((((g * h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w) := by
    rw [e1, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  constructor
  · intro H; rw [e2]; exact hi.mul H
  · intro H; rw [e1]; exact hi'.mul H

theorem rho_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (w₁ : B₁.A) (w₂ : B₂.A),
    (B₁.prod B₂).rho ((w₁, w₂) : B₁.A × B₂.A) = B₁.rho w₁ * B₂.rho w₂ := by
  intro K B₁ B₂ w₁ w₂
  unfold InvAlg.rho
  refine card_prod ((intUnits K.O (B₁.prod B₂).A).subgroupOf (B₁.prod B₂).T) _ _ (torusEquiv B₁ B₂) ?_
    (fun g : (B₁.prod B₂).T => IsIntegral K.O ((((g : (B₁.prod B₂).Aˣ)⁻¹ : (B₁.prod B₂).Aˣ) * (show (B₁.prod B₂).A from (w₁, w₂)) : (B₁.prod B₂).A)))
    (fun g : B₁.T => IsIntegral K.O ((((g : B₁.Aˣ)⁻¹ : B₁.Aˣ) * w₁ : B₁.A)))
    (fun g : B₂.T => IsIntegral K.O ((((g : B₂.Aˣ)⁻¹ : B₂.Aˣ) * w₂ : B₂.A)))
    ?_ (inv_mul_int B₁ w₁) (inv_mul_int B₂ w₂)
  · intro g
    simp only [Subgroup.mem_subgroupOf]
    show (IsIntegral K.O (show B₁.A × B₂.A from ((g : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A)) ∧ IsIntegral K.O (show B₁.A × B₂.A from (((g : (B₁.prod B₂).Aˣ)⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A))) ↔ _
    rw [IsIntegral.pair_iff, IsIntegral.pair_iff]
    exact ⟨fun ⟨⟨a, b⟩, ⟨c, d⟩⟩ => ⟨⟨a, c⟩, ⟨b, d⟩⟩, fun ⟨⟨a, c⟩, ⟨b, d⟩⟩ => ⟨⟨a, b⟩, ⟨c, d⟩⟩⟩
  · intro g
    show IsIntegral K.O (show B₁.A × B₂.A from ((((g : (B₁.prod B₂).Aˣ)⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A) * (show (B₁.prod B₂).A from (w₁, w₂)))) ↔ _
    rw [IsIntegral.pair_iff]
    exact Iff.rfl

end GlobalTheory.RhoProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualHermitianLatticeBasisExists
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.SelfDualLattice

section Forms

variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
  {h : V → V → K.E}

def formL (hadd : ∀ x y z, h (x + y) z = h x z + h y z) (hsmul : ∀ (c : K.E) x z, h (c • x) z = c * h x z)
    (z : V) : V →ₗ[K.E] K.E where
  toFun x := h x z
  map_add' x y := hadd x y z
  map_smul' c x := hsmul c x z

end Forms

end GlobalTheory.SelfDualLattice

namespace GlobalTheory.SelfDualLattice

variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
  {h : V → V → K.E}

end GlobalTheory.SelfDualLattice

namespace GlobalTheory.SelfDualLattice

theorem exists_orthonormal_family (K : UQ)
    (hN : ∀ u : K.Oˣ, K.c (algebraMap K.O K.E u) = algebraMap K.O K.E u →
      ∃ z : K.Oˣ, algebraMap K.O K.E u = algebraMap K.O K.E z * K.c (algebraMap K.O K.E z))
    (hT : ∃ z : K.O, algebraMap K.O K.E z + K.c (algebraMap K.O K.E z) = 1) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
      [Module.Finite K.E V] (h : V → V → K.E), Module.finrank K.E V = n →
      (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) →
      (∀ x y, h y x = K.c (h x y)) → ∀ L : Submodule K.O V, L.FG →
      Submodule.span K.E (L : Set V) = ⊤ →
      (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
      ∃ m, ∃ v : Fin m → V, (∀ i j, h (v i) (v j) = if i = j then 1 else 0) ∧
        Submodule.span K.O (Set.range v) = L := by
  first
  | exact @_root_.GlobalTheory.UnitPairNorm.main
  | exact _root_.GlobalTheory.UnitPairNorm.main
  | (apply _root_.GlobalTheory.UnitPairNorm.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitPairNorm.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitPairNorm.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitPairNorm.main ..)

end GlobalTheory.SelfDualLattice

namespace GlobalTheory.SelfDualLattice

theorem exists_orthonormal_basis : ∀ (K : UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [Module.Finite K.E V] (h : V → V → K.E),
    (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) →
    (∀ x y, h y x = K.c (h x y)) → ∀ L : Submodule K.O V, L.FG →
    Submodule.span K.E (L : Set V) = ⊤ →
    (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V, Submodule.span K.O (Set.range b) = L ∧
      ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  intro K V _ _ _ _ _ h hadd hsmul hsym L hfg hspan hdual
  obtain ⟨hN, hT, -, -⟩ := GlobalTheory.T.unramifiedQuadratic_norms_trace_uniformizer_facts K
  obtain ⟨m, v, hvo, hvs⟩ := exists_orthonormal_family K hN hT _ V h rfl hadd hsmul hsym L hfg hspan hdual
  have hli : LinearIndependent K.E v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (formL hadd hsmul (v i)) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    change ∑ j, g j * h (v j) (v i) = 0 at this
    simpa [hvo] using this
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range v) := by
    rw [← hspan, ← hvs, Submodule.span_span_of_tower]
  set b0 := Module.Basis.mk hli hsp with hb0
  have hm : m = Module.finrank K.E V := by
    rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
  refine ⟨b0.reindex (finCongr hm), ?_, ?_⟩
  · rw [Module.Basis.range_reindex, hb0, Module.Basis.coe_mk, hvs]
  · intro i j
    simp only [Module.Basis.reindex_apply, hb0, Module.Basis.coe_mk, hvo]
    simp

end GlobalTheory.SelfDualLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityLatticeCountRelation
section
noncomputable section
namespace GlobalTheory.PhiGam.Count
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

section
variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

theorem exists_le_sup (P Q : Submodule k U) [FiniteDimensional k (P.map Q.mkQ)] :
    ∃ F : Submodule k U, FiniteDimensional k F ∧ P ≤ F ⊔ Q := by
  obtain ⟨σ, hσ⟩ := Q.mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ Q)
  refine ⟨(P.map Q.mkQ).map σ, inferInstance, fun p hp => ?_⟩
  refine Submodule.mem_sup.2 ⟨σ (Q.mkQ p), ⟨_, ⟨p, hp, rfl⟩, rfl⟩, p - σ (Q.mkQ p), ?_, by abel⟩
  have h : Q.mkQ (σ (Q.mkQ p)) = Q.mkQ p := LinearMap.congr_fun hσ _
  exact (Submodule.Quotient.eq _).mp h.symm

theorem finite_of_le_sup {P Q F : Submodule k U} [FiniteDimensional k F] (h : P ≤ F ⊔ Q) :
    FiniteDimensional k (↥P ⧸ Q.submoduleOf P) := by
  have hker : LinearMap.ker (Q.mkQ ∘ₗ P.subtype) = Q.submoduleOf P := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
  have hle : LinearMap.range (Q.mkQ ∘ₗ P.subtype) ≤ F.map Q.mkQ := by
    rintro _ ⟨⟨p, hp⟩, rfl⟩
    obtain ⟨f, hf, q, hq, rfl⟩ := Submodule.mem_sup.1 (h hp)
    refine ⟨f, hf, ?_⟩
    change Q.mkQ f = Q.mkQ (f + q)
    rw [map_add (f := _), show Q.mkQ q = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hq, add_zero]
  haveI : FiniteDimensional k (LinearMap.range (Q.mkQ ∘ₗ P.subtype)) :=
    Submodule.finiteDimensional_of_le hle
  rw [← hker]
  exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm

theorem gmult_eq_zero (T : Module.End k U) {P Q M : Submodule k U} (hPM : P ≤ M) (hM : ∀ p ∈ M, T p ∈ M)
    (x : k) (h : ∀ p ∈ M, T p - x • p ∈ Q → p ∈ Q) (hQ : ∀ p ∈ Q, T p ∈ Q) : gmult T P Q x = 0 := by
  set S : Module.End k U := T - algebraMap k (Module.End k U) x with hS
  have hSa : ∀ p, S p = T p - x • p := fun p => by simp [hS, Module.algebraMap_end_apply]
  have key : ∀ m : ℕ, ∀ p ∈ M, (S ^ m) p ∈ Q → p ∈ Q := by
    intro m
    induction m with
    | zero => intro p _ hp; simpa using hp
    | succ m ih =>
      intro p hp hq
      rw [pow_succ, Module.End.mul_apply] at hq
      have h1 : S p ∈ M := by rw [hSa]; exact M.sub_mem (hM p hp) (M.smul_mem _ hp)
      exact h p hp (hSa p ▸ ih _ h1 hq)
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m p hp => ?_
    rw [Submodule.mem_comap] at hp ⊢
    rw [pow_succ', Module.End.mul_apply, hSa]
    exact Q.sub_mem (hQ _ hp) (Q.smul_mem _ hp)
  have hle : P ⊓ ⨆ m : ℕ, Q.comap (S ^ m) ≤ Q := by
    rintro p ⟨hp, hq⟩
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 hq
    exact key m p (hPM hp) hm
  unfold gmult
  rw [← hS, Submodule.submoduleOf_eq_top.2 hle]
  exact Module.finrank_zero_of_subsingleton

end

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem exists_le_sup_sh {N : Submodule k⟦X⟧ V} (hN : IsLat N) (m : ℕ) :
    ∃ F : Submodule k V, FiniteDimensional k F ∧
      N.restrictScalars k ≤ F ⊔ (sh m N).restrictScalars k := by
  induction m with
  | zero => exact ⟨⊥, inferInstance, by simp [sh_zero_eq]⟩
  | succ m ih =>
    obtain ⟨F, hF, h⟩ := ih
    haveI := Window.finite_quot (hN.shift m).1
    obtain ⟨F', hF', h'⟩ := exists_le_sup ((sh m N).restrictScalars k) ((sh 1 (sh m N)).restrictScalars k)
    rw [sh_sh_eq, add_comm] at h'
    refine ⟨F ⊔ F', inferInstance, h.trans ?_⟩
    rw [sup_assoc, Nat.cast_succ]
    exact sup_le_sup_left h' _

theorem graded_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (b : ℤ) (x : k) (h : sen g N (x + b) = 0) :
    ∀ y ∈ sh b N, nab g y - x • y ∈ sh (b + 1) N → y ∈ sh (b + 1) N := by
  haveI := Window.finite_quot hN
  obtain ⟨h1, -⟩ := Window.bij_of_gmult_zero (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
    (fun p hp => Window.nab_mem hC hp) (fun p hp => Window.nab_mem_sh R hg hC 1 hp) (x + b) h
  have hv : vv k ≠ 0 := vv_ne_zero k
  intro y hx hx'
  obtain ⟨n, hn, rfl⟩ := mem_sh_iff_exists.mp hx
  obtain ⟨n', hn', e⟩ := Window.nab_shift R hg hC b hn
  obtain ⟨t, ht, e'⟩ := mem_sh_iff_exists.mp hx'
  have hc : x • vv k ^ b • n = vv k ^ b • x • n := by
    rw [← smul_assoc, const_smul_eq, mul_comm, mul_smul, ← mul_one (algebraMap k k⸨X⸩ x), ← const_smul_eq,
      smul_assoc, one_smul]
  rw [e, hc, zpow_add_one₀ hv, mul_smul, ← smul_sub] at e'
  have e2 := smul_right_injective V (zpow_ne_zero b hv) e'
  have : n ∈ sh 1 N := h1 n hn (mem_sh_iff_exists.mpr ⟨t - n', N.sub_mem ht hn', by
    rw [zpow_one, smul_sub, e2, add_smul]; abel⟩)
  obtain ⟨r, hr, rfl⟩ := mem_sh_iff_exists.mp this
  exact mem_sh_iff_exists.mpr ⟨r, hr, by rw [zpow_add₀ hv, mul_smul]⟩

theorem window_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (x : k) (s : ℕ) (h : ∀ j : ℕ, 1 ≤ j → j ≤ s → sen g N (x - j) = 0) :
    ∀ y ∈ sh (-s) N, nab g y - x • y ∈ N → y ∈ N := by
  induction s with
  | zero => intro y hy _; simpa [sh_zero_eq] using hy
  | succ s ih =>
    intro y hy hy'
    refine ih (fun j h1 h2 => h j h1 (Nat.le_succ_of_le h2)) y ?_ hy'
    have e : (-((s + 1 : ℕ) : ℤ)) + 1 = -(s : ℤ) := by push_cast; ring
    have := graded_inj R hg hN hC (-((s + 1 : ℕ) : ℤ)) x (by
      rw [Int.cast_neg, Int.cast_natCast, ← sub_eq_add_neg]; exact h _ (Nat.succ_pos s) le_rfl) y hy
    rw [e] at this
    refine this (sh_le_sh_of_le (a := 0) (by omega) N ?_)
    rwa [sh_zero_eq]

theorem sen_count : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ s : ℕ, P ≤ sh (-s) Q → ∀ x : k, sen g P x + qmult g P Q (x + 1) = sen g Q x + qmult g P Q x ∧ (qmult g P Q x ≠ 0 → ∃ j : ℕ, 1 ≤ j ∧ j ≤ s ∧ sen g Q (x - j) ≠ 0) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg P Q hP hQ hQP cP cQ s hs x
  constructor
  · have h1 : ∀ N : Submodule k⟦X⟧ V, sh 1 N ≤ N := fun N => by
      have := sh_le_sh_of_le (a := 1) (b := 0) (by norm_num) N
      rwa [sh_zero_eq] at this
    obtain ⟨F, hF, hle⟩ := exists_le_sup_sh hP (s + 1)
    have h2 : sh ((s + 1 : ℕ) : ℤ) P ≤ sh 1 Q := by
      have := sh_le_sh ((s + 1 : ℕ) : ℤ) hs
      rwa [sh_sh_eq, show ((s + 1 : ℕ) : ℤ) + -(s : ℤ) = 1 by push_cast; ring] at this
    have hfin : FiniteDimensional k (↥(P.restrictScalars k) ⧸
        ((sh 1 Q).restrictScalars k).submoduleOf (P.restrictScalars k)) :=
      finite_of_le_sup (F := F) (hle.trans (sup_le_sup_left (fun _ hy => h2 hy) _))
    have a1 := GlobalTheory.PhiGam.GmultAdd.main (nab g) (P.restrictScalars k) ((sh 1 P).restrictScalars k)
      ((sh 1 Q).restrictScalars k) (fun _ hy => sh_le_sh 1 hQP hy) (fun _ hy => h1 P hy)
      (fun _ hy => Window.nab_mem cP hy) (fun _ hy => Window.nab_mem_sh R hg cP 1 hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ 1 hy) hfin x
    have a2 := GlobalTheory.PhiGam.GmultAdd.main (nab g) (P.restrictScalars k) (Q.restrictScalars k)
      ((sh 1 Q).restrictScalars k) (fun _ hy => h1 Q hy) (fun _ hy => hQP hy)
      (fun _ hy => Window.nab_mem cP hy) (fun _ hy => Window.nab_mem cQ hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ 1 hy) hfin x
    rw [← _root_.GlobalTheory.PhiGam.QuotShift.main R g hg P Q hP hQ hQP cP cQ x]
    unfold sen qmult
    omega
  · intro hne
    by_contra hno
    push Not at hno
    exact hne (gmult_eq_zero (nab g) (M := (sh (-s) Q).restrictScalars k) (fun _ hy => hs hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ _ hy) x (window_inj R hg hQ.1 cQ x s hno)
      (fun _ hy => Window.nab_mem cQ hy))

end GlobalTheory.PhiGam.Count
end
end

