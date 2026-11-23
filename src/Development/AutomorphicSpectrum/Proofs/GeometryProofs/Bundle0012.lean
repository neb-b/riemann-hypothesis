module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinInverseIsLocalizationAwayStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_inverse_is_localization_away : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (A S' : Subalgebra ℚ Ω) (G : Set Ω), A = Algebra.adjoin ℚ G →
    ∀ (g : A), g ≠ 0 → S' = Algebra.adjoin ℚ (insert (g : Ω)⁻¹ G) → ∀ (hle : A ≤ S'),
    @IsLocalization.Away A _ g S' _ (Subalgebra.inclusion hle).toRingHom.toAlgebra := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.adjoin_inv_isLocalization_away | exact GlobalTheory.CompanionTheory.Ggeo.adjoin_inv_isLocalization_away | (intros; apply GlobalTheory.CompanionTheory.Ggeo.adjoin_inv_isLocalization_away <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DomBy
section
noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.OrVert

def DomBy {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (W : Subring Ω') (i : Ω →+* Ω')
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) : Prop :=
  (∀ a ∈ regAt ξ q, i a ∈ W) ∧ ∀ a ∈ regAt ξ q, a ≠ 0 → (i a)⁻¹ ∈ W → a⁻¹ ∈ regAt ξ q

end GlobalTheory.CompanionTheory.Ar.OrVert
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EpiRingHomFieldClosure
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem epi_subfield_closure_range_eq_top : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F),
    (∀ (T : Type) [CommRing T] (g₁ g₂ : F →+* T), g₁.comp β = g₂.comp β → g₁ = g₂) →
    Subfield.closure (Set.range β) = ⊤ :=
  PositivityTheory.UnitarySelfGeneration.subfield_closure_eq_top_of_epi

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEigenOpDiscr
section
open GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sandwich.Sep

open NumberField Matrix

private theorem exists_discr_dual_basis_of_discr_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (E : Type) [Field E]
    [NumberField E] (ω : Module.Basis ι ℤ (𝓞 E)) (hd : Algebra.discr ℤ ω ≠ 0) :
    ∃ b : ι → 𝓞 E, ∑ i, ω i * b i = ((Algebra.discr ℤ ω : ℤ) : 𝓞 E) ∧
      ∀ x : 𝓞 E, ∀ i, x * b i = ∑ j, ((ω.repr (x * ω j) i : ℤ) : 𝓞 E) * b j := by
  obtain ⟨T, hT⟩ : ∃ T, T = Algebra.traceMatrix ℤ ω := ⟨_, rfl⟩
  have hTsymm : ∀ j k, T j k = T k j := fun j k => by
    simp only [hT, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    rw [mul_comm]
  have hAT : T.adjugate * T = Algebra.discr ℤ ω • (1 : Matrix ι ι ℤ) := by
    rw [Matrix.adjugate_mul, Algebra.discr_def, hT]

  have e1 : ∀ (c : ℤ) (y : 𝓞 E), Algebra.trace ℤ (𝓞 E) ((c : 𝓞 E) * y) =
      c * Algebra.trace ℤ (𝓞 E) y := by
    intro c y
    rw [← zsmul_eq_mul, map_zsmul, smul_eq_mul]
  have htrω : ∀ z : 𝓞 E, ∀ k, Algebra.trace ℤ (𝓞 E) (z * ω k) = ∑ j, ω.repr z j * T j k := by
    intro z k
    conv_lhs => rw [← ω.sum_repr z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_zsmul, smul_eq_mul, hT, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply]

  obtain ⟨b, hb⟩ : ∃ b : ι → 𝓞 E, b = fun i => ∑ k, (T.adjugate i k : 𝓞 E) * ω k := ⟨_, rfl⟩
  have hDB : ∀ z : 𝓞 E, ∀ i, Algebra.trace ℤ (𝓞 E) (z * b i) = Algebra.discr ℤ ω * ω.repr z i := by
    intro z i
    calc Algebra.trace ℤ (𝓞 E) (z * b i)
        = ∑ k, T.adjugate i k * Algebra.trace ℤ (𝓞 E) (z * ω k) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [hb, Finset.mul_sum, map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_left_comm, e1]
      _ = ∑ k, T.adjugate i k * ∑ j, ω.repr z j * T j k := by simp only [htrω]
      _ = ∑ j, ω.repr z j * (T.adjugate * T) i j := by
          simp only [Matrix.mul_apply, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          rw [hTsymm j k]
          ring
      _ = Algebra.discr ℤ ω * ω.repr z i := by
          rw [hAT]
          simp [Matrix.smul_apply, Matrix.one_apply]
          try ring
  have hnd : ∀ s : 𝓞 E, (∀ l, Algebra.trace ℤ (𝓞 E) (s * ω l) = 0) → s = 0 := by
    intro s hs
    have hb0 : ∀ i, Algebra.trace ℤ (𝓞 E) (s * b i) = 0 := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hb, Finset.mul_sum, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [mul_left_comm, e1, hs, mul_zero]
    have hr : ∀ i, ω.repr s i = 0 := fun i => by
      have h := hDB s i
      rw [hb0 i] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hd
    rw [← ω.sum_repr s]
    simp [hr]
  have htr : ∀ y : 𝓞 E, Algebra.trace ℤ (𝓞 E) y = ∑ i, ω.repr (y * ω i) i := by
    intro y
    rw [Algebra.trace_eq_matrix_trace ω, Matrix.trace]
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  refine ⟨b, ?_, ?_⟩
  · apply sub_eq_zero.mp
    apply hnd
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sub_mul, map_sub, Finset.sum_mul, map_sum, e1, htr (ω l)]
    have h : ∀ i, Algebra.trace ℤ (𝓞 E) (ω i * b i * ω l) =
        Algebra.discr ℤ ω * ω.repr (ω l * ω i) i := fun i => by
      rw [mul_right_comm, hDB, mul_comm (ω i)]
    simp only [h, Finset.mul_sum, sub_self]
  · intro x i
    apply sub_eq_zero.mp
    apply hnd
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
    have h1 : Algebra.trace ℤ (𝓞 E) (x * b i * ω l) = Algebra.discr ℤ ω * ω.repr (x * ω l) i := by
      rw [mul_right_comm, hDB]
    have h2 : ∀ j, Algebra.trace ℤ (𝓞 E) (((ω.repr (x * ω j) i : ℤ) : 𝓞 E) * b j * ω l) =
        ω.repr (x * ω j) i * (Algebra.discr ℤ ω * ω.repr (ω l) j) := fun j => by
      rw [mul_assoc, e1, mul_comm (b j), hDB]
    simp only [h1, h2, ω.repr_self, Finsupp.single_apply]
    simp
    try ring

theorem exists_sep_element (E : Type) [Field E] [NumberField E] :
    ∃ (n : ℕ) (a b : Fin n → 𝓞 E), ∑ i, a i * b i = ((discr E : ℤ) : 𝓞 E) ∧
      ∀ x : 𝓞 E, ∃ m : Matrix (Fin n) (Fin n) ℤ, (∀ i, x * a i = ∑ j, (m i j : 𝓞 E) * a j) ∧
        ∀ i, x * b i = ∑ j, (m j i : 𝓞 E) * b j := by
  classical
  let ω := (RingOfIntegers.basis E).reindex (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E)))
  have hdisc : Algebra.discr ℤ ω = discr E := by
    simp only [ω, Module.Basis.coe_reindex]
    rw [Algebra.discr_reindex]
  obtain ⟨b, hsum, hb⟩ := exists_discr_dual_basis_of_discr_ne_zero E ω (by rw [hdisc]; exact discr_ne_zero E)
  refine ⟨_, ω, b, by rw [← hdisc]; exact hsum, fun x =>
    ⟨fun i j => ω.repr (x * ω i) j, fun i => ?_, fun i => hb x i⟩⟩
  conv_lhs => rw [← ω.sum_repr (x * ω i)]
  simp [zsmul_eq_mul]

theorem exists_eigen_op_discr (E : Type) [Field E] [NumberField E] :
    ∃ (n : ℕ) (a b : Fin n → 𝓞 E), ∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]
      (ρ : 𝓞 E →+* Module.End R V) (σ : 𝓞 E →+* R),
      (∀ v, ∑ i, σ (b i) • ρ (a i) v ∈ eigSp ρ σ) ∧
        ∀ v ∈ eigSp ρ σ, ∑ i, σ (b i) • ρ (a i) v = ((discr E : ℤ) : R) • v := by
  obtain ⟨n, a, b, hsum, hm⟩ := exists_sep_element E
  refine ⟨n, a, b, fun R _ V _ _ ρ σ => ⟨fun v => ?_, fun v hv => ?_⟩⟩
  · rw [eigSp, Submodule.mem_iInf]
    intro x
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply,
      LinearMap.id_apply]
    obtain ⟨m, hma, hmb⟩ := hm x
    have L : ∀ i, ρ x (ρ (a i) v) = ∑ j, (m i j : R) • ρ (a j) v := fun i => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Module.End.mul_apply, ← map_mul, hma i, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_intCast, Module.End.mul_apply, Module.End.intCast_apply,
        Int.cast_smul_eq_zsmul]
    have Rr : ∀ j, σ x * σ (b j) = ∑ i, (m i j : R) * σ (b i) := fun j => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_mul, hmb j, map_sum]
      simp [map_mul, map_intCast]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    simp only [map_smul, L, Finset.smul_sum, smul_smul, Rr, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  · have hv' : ∀ x, ρ x v = σ x • v := by
      intro x
      rw [eigSp, Submodule.mem_iInf] at hv
      have h := hv x
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
      simpa using h
    simp only [hv', smul_smul, ← Finset.sum_smul]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_intCast σ, ← hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_comm]

end GlobalTheory.CompanionTheory.Ar.Sandwich.Sep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPointLocalizationPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem germ_isUnit_and_surj {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (y : X) (hy : y ∈ U) :
    (∀ a : Γ(X, U), IsUnit (X.presheaf.germ U y hy a) ↔ a ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
    ∀ g : X.presheaf.stalk y, ∃ b c : Γ(X, U), b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      g * X.presheaf.germ U y hy b = X.presheaf.germ U y hy c := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : U)
  have hl : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  refine ⟨fun a => ?_, fun g => ?_⟩
  · exact IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk y)
      (hU.primeIdealOf ⟨y, hy⟩).asIdeal a
  · obtain ⟨⟨c, ⟨b, hb⟩⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl g
    exact ⟨b, c, hb, h⟩

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

theorem genMap_germ {U : X.Opens} (p : Cpt ξ) (hp : p.1 ∈ U) (hg : genPt ξ ∈ U) (a : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp a) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hg a) := by
  have h : X.presheaf.germ U p.1 hp ≫ X.presheaf.stalkSpecializes p.2 = X.presheaf.germ U (genPt ξ) hg :=
    TopCat.Presheaf.germ_stalkSpecializes _ _ _
  simp only [genMap, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← h]
  rfl

theorem genMap_stalkSpecializes (p q : Cpt ξ) (h : q.1 ⤳ p.1) (g : X.presheaf.stalk p.1) :
    genMap ξ q ((X.presheaf.stalkSpecializes h).hom g) = genMap ξ p g := by
  have h2 : X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes q.2 =
      X.presheaf.stalkSpecializes p.2 := TopCat.Presheaf.stalkSpecializes_comp _ _ _
  simp only [genMap]
  rw [← h2]
  rfl

end GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_prime_generisation : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (p : Cpt ξ) (I : Ideal (regAt ξ p)), I.IsPrime → ∃ q : Cpt ξ, q.1 ⤳ p.1 ∧ ∀ a : Ω, a ∈ regAt ξ q ↔ ∃ s : regAt ξ p, s ∉ I ∧ (s : Ω) * a ∈ regAt ξ p := by
  intro X Ω _ ξ hξ p I hI
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := p.1) (U := ⊤) trivial
  have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  let ρ : X.presheaf.stalk p.1 →+* regAt ξ p := (genMap ξ p).rangeRestrict
  have hρ : ∀ r, ((ρ r : regAt ξ p) : Ω) = genMap ξ p r := fun _ => rfl
  have hρs : Function.Surjective ρ := (genMap ξ p).rangeRestrict_surjective
  let J : Ideal (X.presheaf.stalk p.1) := I.comap ρ
  have hJ : J.IsPrime := Ideal.comap_isPrime ρ I
  let gp : Γ(X, U) →+* X.presheaf.stalk p.1 := (X.presheaf.germ U p.1 hpU).hom
  let Q0 : PrimeSpectrum Γ(X, U) := ⟨J.comap gp, Ideal.comap_isPrime gp J⟩
  have hspec : ∀ P Q : PrimeSpectrum Γ(X, U), hU.fromSpec P ⤳ hU.fromSpec Q ↔ P ≤ Q := by
    intro P Q
    rw [PrimeSpectrum.le_iff_specializes]
    exact hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff
  have hqU : hU.fromSpec Q0 ∈ U := by
    have : hU.fromSpec Q0 ∈ Set.range hU.fromSpec := ⟨Q0, rfl⟩
    rwa [hU.range_fromSpec] at this
  have hQ0 : hU.primeIdealOf ⟨_, hqU⟩ = Q0 :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  have hP := hU.fromSpec_primeIdealOf ⟨p.1, hpU⟩
  have hG := hU.fromSpec_primeIdealOf ⟨genPt ξ, hgU⟩
  obtain ⟨hPu, hPs⟩ := germ_isUnit_and_surj hU p.1 hpU
  obtain ⟨hGu, -⟩ := germ_isUnit_and_surj hU (genPt ξ) hgU
  obtain ⟨hQu, hQs⟩ := germ_isUnit_and_surj hU _ hqU
  rw [hQ0] at hQu hQs
  have hunitJ : ∀ r, IsUnit r → r ∉ J := fun r hr hrJ => hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ hrJ hr)

  have hGQ : hU.primeIdealOf ⟨genPt ξ, hgU⟩ ≤ Q0 := by
    intro a ha
    let φ : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
    have hφ : Function.Bijective φ := hξ.bij
    have h0 : φ (X.presheaf.germ U (genPt ξ) hgU a) = 0 := by
      by_contra hne
      obtain ⟨d, hd⟩ := hφ.2 (φ (X.presheaf.germ U (genPt ξ) hgU a))⁻¹
      have h1 : X.presheaf.germ U (genPt ξ) hgU a * d = 1 := by
        apply hφ.1
        rw [map_mul, hd, map_one, mul_inv_cancel₀ hne]
      exact (not_not.mpr ha) ((hGu a).1 (IsUnit.of_mul_eq_one _ h1))
    have h2 : gp a = 0 := by
      apply hξ.inj p
      rw [map_zero, ← h0]
      exact genMap_germ ξ p hpU hgU a
    show gp a ∈ J
    rw [h2]
    exact J.zero_mem
  have hQP : Q0 ≤ hU.primeIdealOf ⟨p.1, hpU⟩ := by
    intro a ha
    by_contra hn
    exact hunitJ _ ((hPu a).2 hn) ha
  have hqp : hU.fromSpec Q0 ⤳ p.1 := by
    have := (hspec _ _).2 hQP
    rwa [hP] at this
  have hgq : genPt ξ ⤳ hU.fromSpec Q0 := by
    have := (hspec _ _).2 hGQ
    rwa [hG] at this
  let q : Cpt ξ := ⟨hU.fromSpec Q0, hgq⟩
  let σ : X.presheaf.stalk p.1 →+* X.presheaf.stalk q.1 := (X.presheaf.stalkSpecializes hqp).hom
  have hσ : ∀ g, genMap ξ q (σ g) = genMap ξ p g := genMap_stalkSpecializes ξ p q hqp
  have hσg : ∀ a : Γ(X, U), σ (X.presheaf.germ U p.1 hpU a) = X.presheaf.germ U q.1 hqU a :=
    fun a => X.presheaf.germ_stalkSpecializes_apply hpU hqp a
  refine ⟨q, hqp, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨b, c, hb, hbc⟩ := hQs g
    refine ⟨ρ (X.presheaf.germ U p.1 hpU b), hb, ⟨X.presheaf.germ U p.1 hpU c, ?_⟩⟩
    rw [hρ, ← hσ, ← hσ, hσg, hσg, ← hbc, map_mul, mul_comm]
  · rintro ⟨s, hs, t, ht⟩
    obtain ⟨r, rfl⟩ := hρs s
    have hrJ : r ∉ J := hs
    obtain ⟨b, c, hb, hbc⟩ := hPs r
    have hbu := (hPu b).2 hb
    have hcJ : X.presheaf.germ U p.1 hpU c ∉ J := by
      rw [← hbc]
      intro h
      exact (hJ.mem_or_mem h).elim hrJ (hunitJ _ hbu)
    have hcu := (hQu c).2 hcJ
    have hσr : IsUnit (σ r) := by
      rw [← hσg, ← hbc, map_mul] at hcu
      exact isUnit_of_mul_isUnit_left hcu
    obtain ⟨u, hu⟩ := hσr
    refine ⟨(↑u⁻¹ : X.presheaf.stalk q.1) * σ t, ?_⟩
    have hne : genMap ξ q (σ r) * genMap ξ q (↑u⁻¹ : X.presheaf.stalk q.1) = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    rw [map_mul, hσ, ht, hρ, ← hσ r, ← _root_.mul_assoc, mul_comm (genMap ξ q _), hne, _root_.one_mul]

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStalkFractionOfGeneric
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_closedPointTo {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (V : X.Opens) (hy : p.1 ∈ V) (hx : genPt ξ ∈ V) (b : Γ(X, V)) :
    genMap ξ p (X.presheaf.germ V p.1 hy b) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hx b) := by
  have h : X.presheaf.germ V (genPt ξ) hx = X.presheaf.germ V p.1 hy ≫ X.presheaf.stalkSpecializes p.2 :=
    (X.presheaf.germ_stalkSpecializes hy p.2).symm
  rw [h]
  rfl

theorem exists_frac_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    ∃ b c : X.presheaf.stalk p.1, genMap ξ p c ≠ 0 ∧ a * genMap ξ p c = genMap ξ p b := by
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
  have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (genPt ξ)) := (X.presheaf.germ U (genPt ξ) hgU).hom.toAlgebra
  have _ : IsLocalization.AtPrime (X.presheaf.stalk (genPt ξ)) (hU.primeIdealOf ⟨genPt ξ, hgU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨genPt ξ, hgU⟩
  obtain ⟨s, rfl⟩ : ∃ s : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom s = a := hξ.bij.2 a
  obtain ⟨⟨r, d⟩, rfl⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf ⟨genPt ξ, hgU⟩).asIdeal.primeCompl s
  refine ⟨X.presheaf.germ U p.1 hpU r, X.presheaf.germ U p.1 hpU d, ?_, ?_⟩
  · rw [genMap_germ_eq_closedPointTo ξ p U hpU hgU]
    have hu := IsLocalization.map_units (X.presheaf.stalk (genPt ξ)) d
    exact (hu.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  · rw [genMap_germ_eq_closedPointTo ξ p U hpU hgU, genMap_germ_eq_closedPointTo ξ p U hpU hgU]
    have h := congrArg (Scheme.stalkClosedPointTo ξ).hom (IsLocalization.mk'_spec (X.presheaf.stalk (genPt ξ)) r d)
    exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans h

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExtendToFractionField
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem extend_to_fraction_field_relay : ∀ (O F L : Type) [CommRing O] [Field F] [CommRing L] (β : O →+* F) (θ : O →+* L), Subfield.closure (Set.range β) = ⊤ → (∀ b, β b ≠ 0 → IsUnit (θ b)) → (∀ a, β a = 0 → θ a = 0) → ∃ χ : F →+* L, χ.comp β = θ :=
  PositivityTheory.UnitarySelfGeneration.extends_to_fraction_field

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_genMap_germ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (U : X.Opens) (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U) (s : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp s) = genMap ξ q (X.presheaf.germ U q.1 hq s) := by
  have h : ∀ (r : Cpt ξ) (hr : r.1 ∈ U), genMap ξ r (X.presheaf.germ U r.1 hr s) =
      (Scheme.stalkClosedPointTo ξ).hom
        (X.presheaf.germ U (genPt ξ) (r.2.mem_open U.isOpen hr) s) := by
    intro r hr
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hr r.2 s)
  rw [h p hp, h q hq]

theorem exists_open_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (a : Ω) (ha : a ∈ regAt ξ p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  obtain ⟨g, rfl⟩ := ha
  obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  exact ⟨U, hU, fun q hq => ⟨_, genMap_germ_eq_genMap_germ ξ U q p hq hU s⟩⟩

theorem regAt_unitAt_open : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω), (a ∈ regAt ξ p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q) ∧ (unitAt ξ p a → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → unitAt ξ q a) := by
  intro X Ω _ ξ p a
  refine ⟨exists_open_mem_regAt ξ p a, ?_⟩
  rintro ⟨h0, h1, h2⟩
  obtain ⟨U, hU, HU⟩ := exists_open_mem_regAt ξ p a h1
  obtain ⟨V, hV, HV⟩ := exists_open_mem_regAt ξ p _ h2
  exact ⟨U ⊓ V, ⟨hU, hV⟩, fun q hq => ⟨h0, HU q hq.1, HV q hq.2⟩⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkSpecializes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegAtMono

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genMap_stalkSpecializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ) (h : q.1 ⤳ p.1)
    (x : X.presheaf.stalk p.1) :
    genMap ξ q ((X.presheaf.stalkSpecializes h).hom x) = genMap ξ p x := by
  have e := X.presheaf.stalkSpecializes_comp q.2 h
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (congrArg (fun φ => φ.hom x) e)

theorem genMap_germ_eq (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ) (h : q.1 ⤳ p.1)
    (U : X.Opens) (hp : p.1 ∈ U) (hq : q.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom t) = genMap ξ p ((X.presheaf.germ U p.1 hp).hom t) := by
  rw [← genMap_stalkSpecializes ξ p q h, ← CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes]

theorem unitAt_of_isUnit (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) {x : X.presheaf.stalk q.1}
    (hx : IsUnit x) : unitAt ξ q (genMap ξ q x) := by
  obtain ⟨u, rfl⟩ := hx
  refine ⟨(u.isUnit.map (genMap ξ q)).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ), ?_⟩⟩
  exact map_units_inv (genMap ξ q) u

theorem regAt_mono :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ), q.1 ⤳ p.1 →
      regAt ξ p ≤ regAt ξ q ∧
        (IsCptGen ξ → ∀ a ∈ regAt ξ q, ∃ s ∈ regAt ξ p, unitAt ξ q s ∧ s * a ∈ regAt ξ p) := by
  intro X Ω _ ξ p q h
  refine ⟨?_, fun _ => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, genMap_stalkSpecializes ξ p q h x⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hp, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p.1) isOpen_univ
    have hU : IsAffineOpen U := hU
    have hq : q.1 ∈ U := h.mem_open U.2 hp
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨q.1, hq⟩ : U)
    have hloc := hU.isLocalization_stalk ⟨q.1, hq⟩
    obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl
      (S := X.presheaf.stalk q.1) x
    have hu : IsUnit ((X.presheaf.germ U q.1 hq).hom t.1) :=
      IsLocalization.map_units (X.presheaf.stalk q.1) t
    have e' : x * (X.presheaf.germ U q.1 hq).hom t.1 = (X.presheaf.germ U q.1 hq).hom r := e
    refine ⟨genMap ξ q ((X.presheaf.germ U q.1 hq).hom t.1), ?_, unitAt_of_isUnit ξ q hu, ?_⟩
    · exact ⟨_, (genMap_germ_eq ξ p q h U hp hq _).symm⟩
    · rw [mul_comm, ← map_mul, e']
      exact ⟨_, (genMap_germ_eq ξ p q h U hp hq _).symm⟩

end GlobalTheory.CompanionTheory.Ar.RegAtMono
end

