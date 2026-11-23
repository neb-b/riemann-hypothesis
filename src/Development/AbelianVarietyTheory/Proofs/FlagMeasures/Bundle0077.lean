module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnipotent
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardGluingHomKernelsLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GluingKernels

theorem encard_le_of_param {R D β : Type} [CommRing R] [AddCommGroup D] [Module R D] [Finite D]
    (m j : ℕ) (Φ : (Fin m → D) → β) (T : Set β)
    (hT : ∀ t ∈ T, ∃ I : Submodule R D, Nat.card I = j ∧ ∃ x : Fin m → D, (∀ i, x i ∈ I) ∧ Φ x = t) :
    T.encard ≤ ((Nat.card (Submodule R D) * j ^ m : ℕ) : ℕ∞) := by
  haveI : Finite (Submodule R D) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule R D))
  let A := Σ I : {I : Submodule R D // Nat.card I = j}, (Fin m → I.1)
  let Ψ : A → β := fun a => Φ fun i => (a.2 i : D)
  have hsub : T ⊆ Ψ '' Set.univ := by
    intro t ht
    obtain ⟨I, hI, x, hx, rfl⟩ := hT t ht
    exact ⟨⟨⟨I, hI⟩, fun i => ⟨x i, hx i⟩⟩, trivial, rfl⟩
  haveI : Fintype {I : Submodule R D // Nat.card I = j} := Fintype.ofFinite _
  have hA : Nat.card A ≤ Nat.card (Submodule R D) * j ^ m := by
    have h1 : Nat.card A = ∑ I : {I : Submodule R D // Nat.card I = j}, j ^ m := by
      rw [Nat.card_sigma]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [Nat.card_fun, I.2, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [h1, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
    exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective _ Subtype.val_injective)
  calc T.encard ≤ (Ψ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set A).encard := Set.encard_image_le _ _
    _ = (Nat.card A : ℕ∞) := by
      rw [Set.encard_univ, ENat.card_eq_coe_natCard]
    _ ≤ _ := by exact_mod_cast hA

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E}
  {r k : ℕ} (S : Frames L r k)

theorem sat_gens (d : S.Datum) (Λ : Submodule L.O S.V) (hΛ : S.IsTerm d Λ) :
    ∃ b : Fin ((r + 1) + (r + 1)) → S.V, S.sat Λ = Submodule.span L.O (Set.range b) := by
  obtain ⟨hSD, hW, -, h1, h2, hli, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ
  haveI : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.1
  have hfg : (S.sat Λ).FG := by
    haveI : IsNoetherian L.O Λ := isNoetherian_of_fg_of_noetherian Λ hSD.1.1
    exact (isNoetherian_submodule.1 this) _ inf_le_left
  have hsp := (_root_.GlobalTheory.FrameGram.main L r k S _ hW.2.2.1 _ hW.2.2.2.1).2.2
  set y := Sum.elim (S.fr d Λ) (S.fr' d Λ) with hy
  have hr : Set.range (y ∘ finSumFinEquiv.symm) = Set.range y :=
    finSumFinEquiv.symm.surjective.range_comp y
  obtain ⟨b, -, hb⟩ := GlobalTheory.OrderBasis.order_basis L (y ∘ finSumFinEquiv.symm)
    (hli.comp _ finSumFinEquiv.symm.injective) (S.sat Λ) hfg (by
      rw [hr]
      apply le_antisymm
      · rw [Submodule.span_le]
        intro x hx
        have hx2 : x ∈ S.ME := hx.2
        rw [← hsp] at hx2
        refine (Submodule.span_le.2 ?_) hx2
        rintro _ ⟨i | i, rfl⟩
        · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
        · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
            (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
      · apply Submodule.span_mono
        rintro _ ⟨i | i, rfl⟩
        · have := (h1 (r + 1) le_rfl (S.fr d Λ i)).2 (Submodule.subset_span ⟨i, i.2, rfl⟩)
          exact ⟨this.1, Submodule.mem_sup_left this.2⟩
        · have := (h2 (r + 1) le_rfl (S.fr' d Λ i)).2 (Submodule.subset_span ⟨i, i.2, rfl⟩)
          exact ⟨this.1, Submodule.mem_sup_right this.2⟩)
  exact ⟨b, hb⟩

theorem tauRel_sum (d : S.Datum) (Λ : Submodule L.O S.V) (hΛ : S.IsTerm d Λ) {ι : Type}
    (s : Finset ι) (c : ι → L.O) (w y : ι → S.V) (h : ∀ i, S.TauRel d Λ (w i) (y i)) :
    S.TauRel d Λ (∑ i ∈ s, c i • w i) (∑ i ∈ s, c i • y i) := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ hΛ
  induction s using Finset.induction_on with
  | empty => simpa using ((h4 0 (Submodule.zero_mem _)).1 (Submodule.zero_mem _)).2
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact h3 (c a) (c a).2 _ _ _ _ (h a) ih

theorem encard_kernels_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) C (Mh : Submodule L.O S.V) (j : ℕ), ((((fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) '' {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j}).encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (S.a.toNat * (2 * r + 2)) * (j : ℝ≥0∞) ^ (k - 1) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d C Mh j
  rcases Set.eq_empty_or_nonempty
    {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j} with h0 | ⟨Λ₀, h₀, hC₀, hM₀, -⟩
  · rw [h0]; simp
  obtain ⟨-, -, -, -, -, b, -, hb⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ₀ h₀
  obtain ⟨-, -, -, -, -, ⟨i₀, hi₀, hbe⟩, -⟩ := _root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ₀ h₀
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  let M₀ : Submodule L.O Mh := (S.M d Λ₀).comap Mh.subtype
  have hcard : Nat.card (Mh ⧸ M₀) = S.q ^ i₀ := by
    rw [← hbe, Frames.be, hM₀]
    rfl
  haveI : Finite (Mh ⧸ M₀) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨g, hg⟩ := sat_gens S d Λ₀ h₀
  rw [hM₀] at hg
  have hgm : ∀ i, g i ∈ Mh := fun i => by rw [hg]; exact Submodule.subset_span ⟨i, rfl⟩
  have hgen : Submodule.span L.O (Set.range fun i => M₀.mkQ ⟨g i, hgm i⟩) = ⊤ := by
    have h1 : Submodule.span L.O (Set.range fun i => (⟨g i, hgm i⟩ : Mh)) = ⊤ := by
      apply Submodule.map_injective_of_injective Mh.injective_subtype
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
      exact hg.symm
    have h2 : (Set.range fun i => M₀.mkQ ⟨g i, hgm i⟩) =
        M₀.mkQ '' Set.range fun i => (⟨g i, hgm i⟩ : Mh) := by
      rw [← Set.range_comp]; rfl
    rw [h2, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_mkQ]
  have hsub := (GlobalTheory.SubmoduleCount.card_submodule_and_hom_le L (Mh ⧸ M₀) _ _ hgen).1
  have key := encard_le_of_param (R := L.O) (k - 1) j
    (fun x : Fin (k - 1) → Mh ⧸ M₀ =>
      (LinearMap.ker (Fintype.linearCombination L.O x)).map (Fintype.linearCombination L.O b))
    ((fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) ''
      {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j}) (by
    rintro _ ⟨Λ, ⟨hΛ, hC, hM, hj⟩, rfl⟩
    obtain ⟨t1, t2, -, t4, t5, -⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ hΛ
    rw [hM] at t1 t5
    have hMM : S.M d Λ = S.M d Λ₀ := by
      have hmem : (S.fr d Λ, S.fr' d Λ) ∈ S.frameCls (S.fr d Λ₀) (S.fr' d Λ₀) := by
        have := (GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).1
        have h2 : S.frameCls (S.fr d Λ) (S.fr' d Λ) = S.frameCls (S.fr d Λ₀) (S.fr' d Λ₀) :=
          hC.trans hC₀.symm
        rwa [h2] at this
      exact ((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1 _ hmem).2
    have hbL : ∀ i, b i ∈ S.complementLatticeOfDatum d := fun i => by
      rw [hb]; exact Submodule.subset_span ⟨i, rfl⟩
    choose y hy hty using fun i => t1 (b i) (hbL i)
    refine ⟨((S.Ihat d Λ).comap Mh.subtype).map M₀.mkQ, ?_, fun i => M₀.mkQ ⟨y i, hy i⟩, ?_, ?_⟩
    · rw [← hj, Frames.cardI, hMM,
        ← AddSubgroup.relIndex_addSubgroupOf (L := Mh.toAddSubgroup) t5]
      have hk : (S.M d Λ₀).toAddSubgroup.addSubgroupOf Mh.toAddSubgroup =
          M₀.mkQ.toAddMonoidHom.ker := by
        ext x
        exact (Submodule.Quotient.mk_eq_zero M₀).symm
      rw [hk, AddSubgroup.relIndex_ker]
      rfl
    · intro i
      exact ⟨⟨y i, hy i⟩, Submodule.mem_sup_right (Submodule.subset_span ⟨b i, hbL i, hty i⟩), rfl⟩
    · have hz : ∀ c : Fin (k - 1) → L.O,
          Fintype.linearCombination L.O (fun i => M₀.mkQ ⟨y i, hy i⟩) c = 0 ↔
            S.TauRel d Λ (∑ i, c i • b i) 0 := by
        intro c
        rw [t2 _ _ 0 (tauRel_sum S d Λ hΛ Finset.univ c b y hty), sub_zero, hMM,
          Fintype.linearCombination_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [← map_smul, ← map_sum]
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        simp [M₀]
      ext w
      simp only [Submodule.mem_map, LinearMap.mem_ker, hz, Submodule.mem_inf,
        Submodule.restrictScalars_mem]
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hL : ∑ i, c i • b i ∈ S.complementLatticeOfDatum d := by
          rw [hb]
          exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
        rw [Fintype.linearCombination_apply]
        exact ⟨(t4 _ hL.1).2 ⟨hL, hc⟩, hL.1⟩
      · rintro ⟨hw, hw0⟩
        obtain ⟨hL, ht⟩ := (t4 w hw0).1 hw
        rw [hb] at hL
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hL
        exact ⟨c, ht, Fintype.linearCombination_apply _ _ _⟩)
  have hN : Nat.card (Submodule L.O (Mh ⧸ M₀)) * j ^ (k - 1) ≤
      S.q ^ (S.a.toNat * (2 * r + 2)) * j ^ (k - 1) := by
    refine Nat.mul_le_mul_right _ (hsub.trans ?_)
    rw [hcard, ← pow_mul]
    refine Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul (by omega) (by omega))
  have h3 := key.trans (Nat.cast_le.2 hN)
  have h4 := ENat.toENNReal_le.2 h3
  simpa using h4

end GlobalTheory.HL.GluingKernels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardShortVectorsLe
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass

theorem trace_cast_eq_sum_re {K : Type} [Field K] [NumberField K] (z : K) :
    ((Algebra.trace ℚ K z : ℚ) : ℝ) = ∑ τ : K →ₐ[ℚ] ℂ, (τ z).re := by
  have key := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := z)
  have hre := congrArg Complex.re key
  rw [Complex.re_sum] at hre
  rw [← hre]
  simp

theorem card_algHom_eq_two_mul_fDeg {K : Type} [Field K] [NumberField K] (hK : IsTotallyComplex K) :
    Module.finrank ℚ K = 2 * fDeg K := by
  have := hK
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

theorem finrank_le_trace_of_integral {K : Type} [Field K] [NumberField K] (z : 𝓞 K)
    (hre : ∀ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).im = 0) (hpos : ∀ τ : K →ₐ[ℚ] ℂ, 0 < (τ (z : K)).re) :
    (Module.finrank ℚ K : ℝ) ≤ ∑ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re := by
  classical
  have hprod : ((∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re : ℝ) : ℂ) = ∏ τ : K →ₐ[ℚ] ℂ, τ (z : K) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact Complex.ext (by simp) (by simp [hre τ])
  have hnorm := Algebra.norm_eq_prod_embeddings (K := ℚ) (E := ℂ) (z : K)
  have h2 : ((((Algebra.norm ℤ z : ℤ) : ℚ) : ℝ) : ℂ) = ((∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re : ℝ) : ℂ) := by
    rw [hprod, ← hnorm, Algebra.coe_norm_int]
    simp
  have hN : (((Algebra.norm ℤ z : ℤ) : ℚ) : ℝ) = ∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re :=
    Complex.ofReal_injective h2
  have hP : (0 : ℝ) < ∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re := Finset.prod_pos fun τ _ => hpos τ
  have hN1 : (1 : ℝ) ≤ ∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re := by
    rw [← hN] at hP ⊢
    have h3 : (0 : ℤ) < Algebra.norm ℤ z := by exact_mod_cast hP
    have h4 : (1 : ℤ) ≤ Algebra.norm ℤ z := h3
    exact_mod_cast h4
  have hL := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.traceLower (K →ₐ[ℚ] ℂ) (fun τ => (τ (z : K)).re)
    (fun τ => (hpos τ).le) hN1
  simpa only [AlgHom.card] using hL

theorem finrank_le_of_span_range {K V E : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup E] [Module ℝ E] (ι : V →+ E)
    (hs : Submodule.span ℝ (Set.range ι) = ⊤) :
    Module.finrank ℝ E ≤ Module.finrank ℚ K * Module.finrank K V := by
  classical
  let bV := Module.finBasis K V
  let bK := Module.finBasis ℚ K
  let g : Fin (Module.finrank ℚ K) × Fin (Module.finrank K V) → E := fun p => ι (bK p.1 • bV p.2)
  have hsub : Set.range ι ⊆ Submodule.span ℝ (Set.range g) := by
    rintro _ ⟨v, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← bV.sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← bK.sum_repr (bV.repr v j), Finset.sum_smul, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Rat.smul_def, mul_smul, map_ratCast_smul ι K ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hEq : Submodule.span ℝ (Set.range g) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hs]
    exact Submodule.span_le.mpr hsub
  have hc := finrank_range_le_card (R := ℝ) g
  rw [Set.finrank, hEq, finrank_top] at hc
  simpa [Fintype.card_prod] using hc

theorem encard_shortVectors_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → ∀ B : ℝ, 0 ≤ B → (({x : V | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B}.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + 2 * Real.sqrt B) ^ (2 * Module.finrank K V * fDeg K)) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hPD L hL B hB
  classical
  have hK' := hK
  unfold Formalism.HermitianLatticesTheory.IsCMUnram at hK'
  obtain ⟨hTC, hCM, -⟩ := hK'
  have hPD' := hPD
  unfold PD at hPD'
  have hL' := hL
  unfold IsIntLat at hL'
  have hInt := hL'.2
  unfold Formalism.HermitianLatticesTheory.IsIntegralLat at hInt

  have hreal : ∀ (x : V) (τ : K →+* ℂ), (τ (h x x)).im = 0 := by
    intro x τ
    have e1 := hCM τ (h x x)
    have e2 : star (h x x) = h x x := by
      have := hs.eq x x
      simpa [starRingEnd_apply] using this
    rw [e2] at e1
    exact Complex.conj_eq_iff_im.mp e1.symm
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K := by simp
  have hne : Nonempty (K →ₐ[ℚ] ℂ) :=
    Fintype.card_pos_iff.mp (hcard ▸ Module.finrank_pos)

  have htr_pos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
    intro x hx
    have e := trace_cast_eq_sum_re (h x x)
    have hs' : (0 : ℝ) < ∑ τ : K →ₐ[ℚ] ℂ, (τ (h x x)).re :=
      Finset.sum_pos (fun τ _ => hPD' τ.toRingHom x hx) Finset.univ_nonempty
    rw [← e] at hs'
    exact_mod_cast hs'
  obtain ⟨N, ι, hinner, -, -⟩ := Formalism.HermitianLatticesTheory.final_traceReal K V h hs htr_pos
  have hnorm : ∀ x : V, ‖ι x‖ ^ 2 = ∑ τ : K →ₐ[ℚ] ℂ, (τ (h x x)).re := by
    intro x
    rw [← real_inner_self_eq_norm_sq, hinner, trace_cast_eq_sum_re]

  have hlong : ∀ x ∈ L, x ≠ 0 → (Module.finrank ℚ K : ℝ) ≤ ‖ι x‖ ^ 2 := by
    intro x hx hx0
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hInt x hx x hx)
    have hr' : ((r : 𝓞 K) : K) = h x x := hr
    rw [hnorm, ← hr']
    refine finrank_le_trace_of_integral r (fun τ => ?_) (fun τ => ?_)
    · rw [hr']; exact hreal x τ.toRingHom
    · rw [hr']; exact hPD' τ.toRingHom x hx0

  have hshort : ∀ x : V, (∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B) →
      ‖ι x‖ ^ 2 ≤ (Module.finrank ℚ K : ℝ) * B := by
    intro x hx
    rw [hnorm]
    calc ∑ τ : K →ₐ[ℚ] ℂ, (τ (h x x)).re ≤ ∑ _τ : K →ₐ[ℚ] ℂ, B :=
          Finset.sum_le_sum fun τ _ => hx τ.toRingHom
      _ = (Module.finrank ℚ K : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]

  have hinj : Function.Injective ι := by
    intro a b hab
    by_contra hne'
    have hd : a - b ≠ 0 := sub_ne_zero.mpr hne'
    have h0 : ι (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hp := htr_pos (a - b) hd
    have hq : ‖ι (a - b)‖ ^ 2 = ((Algebra.trace ℚ K (h (a - b) (a - b)) : ℚ) : ℝ) := by
      rw [← real_inner_self_eq_norm_sq, hinner]
    rw [h0, norm_zero] at hq
    have : ((Algebra.trace ℚ K (h (a - b) (a - b)) : ℚ) : ℝ) = 0 := by rw [← hq]; ring
    have : Algebra.trace ℚ K (h (a - b) (a - b)) = 0 := by exact_mod_cast this
    exact absurd this hp.ne'

  set E := EuclideanSpace ℝ (Fin N)
  set Es : Submodule ℝ E := Submodule.span ℝ (Set.range ι) with hEs
  let ι' : V →+ Es := AddMonoidHom.mk' (fun x => ⟨ι x, Submodule.subset_span ⟨x, rfl⟩⟩)
    (fun a b => Subtype.ext (map_add ι a b))
  have hι' : ∀ x, ((ι' x : Es) : E) = ι x := fun x => rfl
  have hspan : Submodule.span ℝ (Set.range ι') = ⊤ := by
    have e : Set.range ι' = ((↑) : Es → E) ⁻¹' (Set.range ι) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, Subtype.ext hx⟩
    rw [e]
    exact Submodule.span_span_coe_preimage
  have hdim : Module.finrank ℝ Es ≤ 2 * Module.finrank K V * fDeg K := by
    have h1 := finrank_le_of_span_range (K := K) (V := V) ι' hspan
    rw [card_algHom_eq_two_mul_fDeg hTC] at h1
    calc Module.finrank ℝ Es ≤ 2 * fDeg K * Module.finrank K V := h1
      _ = 2 * Module.finrank K V * fDeg K := by ring

  set D : ℝ := (Module.finrank ℚ K : ℝ) with hD
  have hD0 : 0 < D := by
    rw [hD]; exact_mod_cast Module.finrank_pos
  set Λ : AddSubgroup Es := L.toAddSubgroup.map ι'
  have hl0 : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hmin : ∀ y ∈ Λ, y ≠ 0 → Real.sqrt D ≤ ‖y‖ := by
    intro y hy hy0
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hy
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hy0 (map_zero ι')
    have e : ‖ι' x‖ = ‖ι x‖ := rfl
    rw [e]
    calc Real.sqrt D ≤ Real.sqrt (‖ι x‖ ^ 2) := Real.sqrt_le_sqrt (hlong x hx hx0)
      _ = ‖ι x‖ := Real.sqrt_sq (norm_nonneg _)
  obtain ⟨hfin, hcount⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.packing Es Λ (Real.sqrt D) (Real.sqrt (D * B))
    hl0 (Real.sqrt_nonneg _) hmin
  have hratio : 2 * Real.sqrt (D * B) / Real.sqrt D = 2 * Real.sqrt B := by
    rw [Real.sqrt_mul hD0.le, mul_div_assoc, mul_div_cancel_left₀ _ hl0.ne']
  rw [hratio] at hcount
  have hbase : (1 : ℝ) ≤ 1 + 2 * Real.sqrt B := by
    have := Real.sqrt_nonneg B
    linarith
  have hpow := pow_le_pow_right₀ hbase hdim

  have hmaps : Set.MapsTo ι' {x | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B}
      {y : Es | y ∈ Λ ∧ ‖y‖ ≤ Real.sqrt (D * B)} := by
    rintro x ⟨hx, hxB⟩
    refine ⟨AddSubgroup.mem_map_of_mem ι' hx, ?_⟩
    have e : ‖ι' x‖ = ‖ι x‖ := rfl
    rw [e]
    have := Real.abs_le_sqrt (hshort x hxB)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hinj' : Set.InjOn ι' {x | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B} := by
    intro a _ b _ hab
    apply hinj
    rw [← hι' a, ← hι' b, hab]
  have hle := Set.encard_le_encard_of_injOn hmaps hinj'
  rw [← hfin.cast_ncard_eq] at hle
  calc ((({x | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B}.encard : ℕ∞) : ℝ≥0∞))
      ≤ (((({y : Es | y ∈ Λ ∧ ‖y‖ ≤ Real.sqrt (D * B)}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞) := by
        exact_mod_cast hle
    _ = ENNReal.ofReal (({y : Es | y ∈ Λ ∧ ‖y‖ ≤ Real.sqrt (D * B)}.ncard : ℝ)) := by
        simp
    _ ≤ ENNReal.ofReal ((1 + 2 * Real.sqrt B) ^ (2 * Module.finrank K V * fDeg K)) :=
        ENNReal.ofReal_le_ofReal (hcount.trans hpow)

end GlobalTheory.Mass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteLatticesBetweenOfSmulLe
section
open NumberField

namespace GlobalTheory

theorem finite_lattices_between_of_smul_le :
    ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → ∀ N : ℕ, 0 < N →
      {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M}.Finite := by
  intro K V _ _ _ _ _ _ M hM N hN
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  let f : V →ₗ[𝓞 K] V := (((N : K)⁻¹) • LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K)
  have hf : ∀ x, f x = (N : K)⁻¹ • x := fun x => rfl
  have hback : ∀ x : V, f ((N : K) • x) = x := by
    intro x; rw [hf, smul_smul, inv_mul_cancel₀ hNK, one_smul]
  have hsm : ∀ x ∈ M, (N : K) • x ∈ M := by
    intro x hx
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx N
  set D := M.map f with hD
  have hMD : M ≤ D := fun x hx => ⟨(N : K) • x, hsm x hx, hback x⟩
  have hsub : {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M} ⊆
      {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ Λ ≤ D} := by
    rintro Λ ⟨h1, h2⟩
    exact ⟨h1, fun x hx => ⟨(N : K) • x, h2 x hx, hback x⟩⟩
  refine Set.Finite.subset ?_ hsub
  have h1 := Formalism.HermitianLatticesTheory.final_finIntermediate V M.toAddSubgroup D.toAddSubgroup hMD ?_
  · refine Set.Finite.of_finite_image (f := Submodule.toAddSubgroup) (h1.subset ?_)
      (Submodule.toAddSubgroup_injective.injOn)
    rintro _ ⟨Λ, ⟨h2, h3⟩, rfl⟩
    exact ⟨h2, h3⟩
  · have f1 : Module.Finite (𝓞 K) D := Module.Finite.iff_fg.mpr (hM.map f)
    have f2 : Module.Finite ℤ D := Module.Finite.trans (𝓞 K) D
    have f3 : AddGroup.FG D.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp f2
    apply AddCommGroup.finite_of_fg_isAddTorsion
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      rw [isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨(N : ℤ), by exact_mod_cast hN.ne', ?_⟩
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      obtain ⟨m, hm, hq⟩ := q.2
      have : (((N : ℤ) • q : D.toAddSubgroup) : V) = m := by
        rw [AddSubgroup.coe_zsmul, ← hq, hf, ← Int.cast_smul_eq_zsmul K, Int.cast_natCast,
          smul_smul, mul_inv_cancel₀ hNK, one_smul]
      rw [this]
      exact hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassEqWeightedSumFibresStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres : ∀ (G α β : Type) [Group G] [MulAction G α] [MulAction G β] (X : Set α) (Y : Set β) (π : α → β), (∀ (g : G) x, π (g • x) = g • π x) → Stable G X → Stable G Y → Set.MapsTo π X Y → (∀ y ∈ Y, Finite (MulAction.stabilizer G y)) → orbMass G X = orbSum G Y (fun y => (((X ∩ π ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞)) := by
  first | exact @GlobalTheory.Mass.orbMass_eq_orbSum_fibre | exact GlobalTheory.Mass.orbMass_eq_orbSum_fibre | (intros; apply GlobalTheory.Mass.orbMass_eq_orbSum_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnipotentStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_unipotent_alt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, {p | n p • A.lat p Λ ≠ A.lat p Λ}.Finite → ((∀ p, n p ∈ (G.S p).N) → ∃ g ∈ G.N, ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) ∧ ((∀ p, n p ∈ (G.S p).N') → ∃ g ∈ G.N', ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) := by
  intro F E _ _ _ _ _ sig A r k G Λ hΛ c hc n hn
  letI := hΛ
  exact GlobalTheory.HL.SAN.strong_approximation_unipotent A r k G Λ inferInstance c hc n hn
end

