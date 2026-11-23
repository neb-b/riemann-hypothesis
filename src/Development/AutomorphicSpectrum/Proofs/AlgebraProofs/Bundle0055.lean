module

public import Mathlib
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0002
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0040

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InvariantOpenChartPreimage
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

theorem IsChart.exists_opens_image_preimage {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens}
    {q : V.toScheme ⟶ Y} (h : IsChart a b V q) (V' : X.Opens) (hV : V' ≤ V)
    (hs : a ⁻¹ᵁ V' = b ⁻¹ᵁ V') : ∃ D : Y.Opens, V.ι ''ᵁ (q ⁻¹ᵁ D) = V' := by
  have := h.isFinite
  have hsat : ∀ u v : V.toScheme, q u = q v → V.ι u ∈ V' → V.ι v ∈ V' := by
    intro u v huv hu
    obtain ⟨p, hpa, hpb⟩ := (h.apply_eq_iff u v).1 huv
    have hp : p ∈ a ⁻¹ᵁ V' := by
      show a p ∈ V'
      rw [hpa]
      exact hu
    rw [hs] at hp
    have hb : b p ∈ V' := hp
    rwa [hpb] at hb
  let C : Set V.toScheme := ((V.ι ⁻¹ᵁ V' : V.toScheme.Opens) : Set V.toScheme)ᶜ
  have hC : IsClosed C := (V.ι ⁻¹ᵁ V').isOpen.isClosed_compl
  have hqC : IsClosed (q '' C) := q.isClosedMap C hC
  refine ⟨⟨(q '' C)ᶜ, hqC.isOpen_compl⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    by_contra hx
    exact hu ⟨u, hx, rfl⟩
  · intro hx
    obtain ⟨u, rfl⟩ : ∃ u, V.ι u = x := by
      rw [← Set.mem_range, Scheme.Opens.range_ι]
      exact hV hx
    refine ⟨u, ?_, rfl⟩
    rintro ⟨v, hv, hvu⟩
    exact hv (hsat u v hvu.symm hx)

end GlobalTheory.CompanionTheory.FreeQuotGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormNotMemPrimeIffStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_not_mem_prime_iff : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (e : B) (p : Ideal A), p.IsPrime → (Algebra.norm A e ∉ p ↔ ∀ q : Ideal B, q.IsPrime → q.comap (algebraMap A B) = p → e ∉ q) := by
  first | exact @GlobalTheory.CompanionTheory.NormPrime.norm_notMem_iff | exact GlobalTheory.CompanionTheory.NormPrime.norm_notMem_iff | (intros; apply GlobalTheory.CompanionTheory.NormPrime.norm_notMem_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackOfGluedCharts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

theorem isPullback_of_preimage_opensRange {X Y Y' : Scheme.{0}} (π : X ⟶ Y') (V : X.Opens)
    (q : V.toScheme ⟶ Y) (em : Y ⟶ Y') [IsOpenImmersion em] (hc : V.ι ≫ π = q ≫ em)
    (hpre : π ⁻¹ᵁ em.opensRange = V) : IsPullback q V.ι em π :=
  IsOpenImmersion.isPullback q V.ι em π hc (by rw [hpre, Scheme.Opens.opensRange_ι])

theorem IsChart.isIso_restrict_lift {P X Y Y' : Scheme.{0}} {a b : P ⟶ X} {π : X ⟶ Y'} {V : X.Opens}
    {q : V.toScheme ⟶ Y} {em : Y ⟶ Y'} [IsOpenImmersion em] (h : IsChart a b V q)
    (hc : V.ι ≫ π = q ≫ em) (hpre : π ⁻¹ᵁ em.opensRange = V) (w : a ≫ π = b ≫ π) :
    IsIso (pullback.lift a b w ∣_ (pullback.snd π π ⁻¹ᵁ V)) := by
  obtain ⟨-, -, -, -, -, a', ha', hsq⟩ := h

  have h1 : IsPullback (b ∣_ V) (a' ≫ V.ι) (V.ι ≫ π) π := by
    have h0 := hsq.paste_horiz (isPullback_of_preimage_opensRange π V q em hc hpre).flip
    rw [← hc] at h0
    exact h0.flip

  have h2 : IsPullback (pullback.snd π π ∣_ V) ((pullback.snd π π ⁻¹ᵁ V).ι ≫ pullback.fst π π)
      (V.ι ≫ π) π :=
    (isPullback_morphismRestrict (pullback.snd π π) V).paste_vert (IsPullback.of_hasPullback π π).flip
  have hdom : pullback.lift a b w ⁻¹ᵁ (pullback.snd π π ⁻¹ᵁ V) = b ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, pullback.lift_snd]

  have key : pullback.lift a b w ∣_ (pullback.snd π π ⁻¹ᵁ V) =
      (P.isoOfEq hdom).hom ≫ (h1.isoIsPullback _ _ h2).hom := by
    apply h2.hom_ext
    · rw [← cancel_mono V.ι]
      simp only [Category.assoc]
      rw [IsPullback.isoIsPullback_hom_fst_assoc]
      simp only [morphismRestrict_ι, morphismRestrict_ι_assoc, pullback.lift_snd,
        Scheme.isoOfEq_hom_ι_assoc]
    · rw [morphismRestrict_ι_assoc, pullback.lift_fst, Category.assoc,
        IsPullback.isoIsPullback_hom_snd, ha', Scheme.isoOfEq_hom_ι_assoc]
  rw [key]
  infer_instance

theorem isPullback_of_isChart {P X Y' : Scheme.{0}} (a b : P ⟶ X) (π : X ⟶ Y') {J : Type}
    (V : J → X.Opens) (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y')
    [∀ j, IsOpenImmersion (em j)] (hch : ∀ j, IsChart a b (V j) (q j))
    (hc : ∀ j, (V j).ι ≫ π = q j ≫ em j) (hpre : ∀ j, π ⁻¹ᵁ (em j).opensRange = V j)
    (hcov : ∀ y : Y', ∃ j, ∃ z : Y j, em j z = y) : IsPullback a b π π := by

  have hV : iSup V = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨j, z, hz⟩ := hcov (π x)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨j, ?_⟩
    rw [← hpre j, Scheme.Hom.mem_preimage]
    exact ⟨z, hz⟩

  have hw : a ≫ π = b ≫ π := by
    refine Scheme.Cover.hom_ext
      (P.openCoverOfIsOpenCover (fun j => b ⁻¹ᵁ V j)
        (by unfold TopologicalSpace.IsOpenCover; exact b.iSup_preimage_eq_top hV)) _ _ fun j => ?_
    obtain ⟨-, -, -, -, -, a', ha', hsq⟩ := hch j
    change (b ⁻¹ᵁ V j).ι ≫ a ≫ π = (b ⁻¹ᵁ V j).ι ≫ b ≫ π
    calc (b ⁻¹ᵁ V j).ι ≫ a ≫ π = a' ≫ (V j).ι ≫ π := by
          rw [← Category.assoc, ← ha', Category.assoc]
      _ = a' ≫ q j ≫ em j := by rw [hc j]
      _ = (b ∣_ V j) ≫ q j ≫ em j := by rw [← Category.assoc, hsq.w, Category.assoc]
      _ = (b ∣_ V j) ≫ (V j).ι ≫ π := by rw [hc j]
      _ = (b ⁻¹ᵁ V j).ι ≫ b ≫ π := by rw [morphismRestrict_ι_assoc]

  have hiso : IsIso (pullback.lift a b hw) := by
    rw [← MorphismProperty.isomorphisms.iff,
      IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
        (fun j => pullback.snd π π ⁻¹ᵁ V j) ((pullback.snd π π).iSup_preimage_eq_top hV)]
    intro j
    rw [MorphismProperty.isomorphisms.iff]
    exact IsChart.isIso_restrict_lift (hch j) (hc j) (hpre j) hw
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso (pullback.lift a b hw))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end GlobalTheory.CompanionTheory.FreeQuotGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupGeneration
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem idealX_le_idealD : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → idealX AA.carrier K t τ ≤ idealD p AA.carrier K t τ := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hq N _ _ _ _ AA hst K t ht hgen τ hτ
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨⟨S, hS, hSst⟩, -⟩ := GlobalTheory.T.stable_hopf_order_subgroup_translation p C v R hv hp F f hq N AA hst K t ht
  obtain ⟨hord, -, hfund, hfunds, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hp F f hq τ hτ
  have hf0 : f ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    rw [hq, pow_zero] at this
    exact lt_irrefl _ this
  have hq1 : 1 < p ^ f := Nat.one_lt_pow hf0 hp1
  have hper1 : τ ^ p ^ f = τ := by
    have : p ^ f = orderOf τ + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have hper : ∀ m, τ ^ p ^ (f * m) = τ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hper1]
  have hprin : ∀ χ : MulChar F R, ∃ c : R, c ≠ 0 ∧ xIdeal S.carrier χ = Ideal.span {c} :=
    fun χ => (GlobalTheory.T.character_ideal_principal_eigen p C v R hv hp F f hq S hSst χ).1
  choose c0 hc0 hc0' using hprin
  let c : ℕ → R := fun n => c0 (τ ^ p ^ n)
  have hcX : ∀ n, idealX AA.carrier K t (τ ^ p ^ n) = Ideal.span {c n} := by
    intro n
    rw [idealX, ← hS]
    exact hc0' _
  have hom := GlobalTheory.T.fundamental_ideal_frobenius_product p C v R hv hp F f hq S hSst τ hτ c (fun n => hc0' _)
  have hcper : ∀ m, c (f * m) = c 0 := by
    intro m
    simp only [c, hper m, pow_zero, pow_one]
  let y : ℕ → NNReal := fun n => v (algebraMap R C (c n))
  have hy1 : ∀ n, y n ≤ 1 := fun n => hv.map_le_one _
  have hy0 : ∀ n, y n ≠ 0 := by
    intro n
    refine (Valuation.ne_zero_iff _).2 fun h => hc0 (τ ^ p ^ n) (hv.hom_inj ?_)
    simpa [c] using h
  have hle : ∀ n, y n ^ p ≤ y (n + 1) := by
    intro n
    obtain ⟨δ, hδ⟩ := (hom n).2.1
    have : y n ^ p = v (algebraMap R C δ) * y (n + 1) := by
      simp only [y]
      rw [← map_pow, ← map_pow, hδ, map_mul, map_mul]
    rw [this]
    exact mul_le_of_le_one_left' (hv.map_le_one _)
  have hpowp : ∀ n, (τ ^ p ^ n) ^ p = τ ^ p ^ (n + 1) := by
    intro n
    rw [← pow_mul, ← pow_succ]
  have hlt : ∀ n, y n ^ p < y (n + 1) → c (n + 1) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + 1)) := by
    intro n h
    have := GlobalTheory.T.stable_hopf_order_subgroup_quotient p C v R hv hp F f hq N AA hst K t ht hgen (τ ^ p ^ n) (hfund n)
      (c n) (c (n + 1)) (hcX n) (by rw [hpowp]; exact hcX (n + 1)) h
    rwa [hpowp] at this
  have heq : ∀ n, y n ^ p = y (n + 1) → c n ∈ idealD p AA.carrier K t (τ ^ p ^ n) →
      c (n + 1) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + 1)) := by
    intro n h hg
    have h1 := GlobalTheory.T.stable_hopf_order_subgroup_length p C v R hv hp F f hq N AA hst K t (τ ^ p ^ n) (c n) hg
    rw [hpowp] at h1
    obtain ⟨δ, hδ⟩ := (hom n).2.1
    have hv1 : v (algebraMap R C δ) = 1 := by
      have h2 : y n ^ p = v (algebraMap R C δ) * y (n + 1) := by
        simp only [y]
        rw [← map_pow, ← map_pow, hδ, map_mul, map_mul]
      rw [h] at h2
      exact (mul_right_cancel₀ (hy0 (n + 1)) (by rw [one_mul]; exact h2)).symm
    have hu : IsUnit δ := by
      refine hv.isUnit_of_one ?_ hv1
      refine IsUnit.mk0 _ fun h0 => ?_
      rw [h0, map_zero] at hv1
      exact zero_ne_one hv1
    rw [hδ] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ hu).1 h1
  have hex : ∃ n, c n ∈ idealD p AA.carrier K t (τ ^ p ^ n) := by
    by_cases h : ∃ n, y n ^ p < y (n + 1)
    · obtain ⟨n, hn⟩ := h
      exact ⟨n + 1, hlt n hn⟩
    · have hall : ∀ n, y n ^ p = y (n + 1) := fun n =>
        le_antisymm (hle n) (not_lt.1 fun h' => h ⟨n, h'⟩)
      have hyn : ∀ n, y n = y 0 ^ p ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [← hall n, ih, ← pow_mul, pow_succ]
      have hyf : y 0 ^ p ^ f = y 0 := by
        rw [← hyn f]
        have := hcper 1
        rw [mul_one] at this
        simp only [y, this]
      have hy01 : y 0 = 1 := by
        refine le_antisymm (hy1 0) (not_lt.1 fun h' => ?_)
        have := pow_lt_self_of_lt_one₀ (pos_iff_ne_zero.2 (hy0 0)) h' hq1
        exact absurd hyf this.ne
      have hu : IsUnit (c 0) := by
        refine hv.isUnit_of_one ?_ hy01
        refine IsUnit.mk0 _ fun h0 => ?_
        have : y 0 = 0 := by simp only [y, h0, map_zero]
        exact hy0 0 this
      have hX : idealX AA.carrier K t τ = ⊤ := by
        have := hcX 0
        rw [pow_zero, pow_one] at this
        rw [this]
        exact Ideal.span_singleton_eq_top.2 hu
      obtain ⟨τ', hτ', hD⟩ := GlobalTheory.T.hopf_order_ideals_eq_top p C v R hv hp F f hq N AA hst K t ht hgen τ hX
      obtain ⟨n, -, rfl⟩ := hfunds τ' hτ'
      exact ⟨n, by rw [hD]; trivial⟩
  obtain ⟨n, hn⟩ := hex
  have hlater : ∀ k, c (n + k) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + k)) := by
    intro k
    induction k with
    | zero => exact hn
    | succ k ih =>
      rcases (hle (n + k)).lt_or_eq with h | h
      · exact hlt _ h
      · exact heq _ h ih
  have hnf : n ≤ f * n := Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hf0)
  have hg := hlater (f * n - n)
  rw [Nat.add_sub_cancel' hnf, hper n] at hg
  have hX := hcX (f * n)
  rw [hper n] at hX
  rw [hX]
  exact (Ideal.span_singleton_le_iff_mem _).2 hg

end GlobalTheory.CompanionTheory.Ar.GR
end

