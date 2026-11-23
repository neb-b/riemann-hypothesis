module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0070
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0067

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableZeroCount
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

open TopologicalSpace

variable {X : Type} [TopologicalSpace X] {d : ℕ} {α : Type} [Fintype α]

def zeroSetIn (A : Set X) (b : α → X → ℂ) (C : Fin d → α → ℂ) : Set X :=
  {z ∈ A | ∀ k, ∑ j, C k j * b j z = 0}

theorem isClosed_meets_compact {K : Set X} (hK : IsCompact K) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) K) :
    IsClosed {C : Fin d → α → ℂ | ∃ z ∈ K, ∀ k, ∑ j, C k j * b j z = 0} := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hF : Continuous fun p : (Fin d → α → ℂ) × K => fun k => ∑ j, p.1 k j * b j p.2 := by
    refine continuous_pi fun k => ?_
    refine continuous_finsetSum _ fun j _ => ?_
    have h1 : Continuous fun p : (Fin d → α → ℂ) × K => p.1 k j :=
      (continuous_apply j).comp ((continuous_apply k).comp continuous_fst)
    have h2 : Continuous fun p : (Fin d → α → ℂ) × K => b j (p.2 : X) :=
      (hb j).comp_continuous (continuous_subtype_val.comp continuous_snd) fun p => p.2.2
    exact h1.mul h2
  have hclosed : IsClosed {p : (Fin d → α → ℂ) × K | ∀ k, ∑ j, p.1 k j * b j p.2 = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_eq ((continuous_apply k).comp hF) continuous_const
  have himage : {C : Fin d → α → ℂ | ∃ z ∈ K, ∀ k, ∑ j, C k j * b j z = 0} =
      Prod.fst '' {p : (Fin d → α → ℂ) × K | ∀ k, ∑ j, p.1 k j * b j p.2 = 0} := by
    ext C
    constructor
    · rintro ⟨z, hz, h⟩
      exact ⟨(C, ⟨z, hz⟩), h, rfl⟩
    · rintro ⟨⟨C', z⟩, h, rfl⟩
      exact ⟨z, z.2, h⟩
  rw [himage]
  exact isClosedMap_fst_of_compactSpace _ hclosed

theorem measurableSet_meets_inter [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X]
    {A B : Set X} (hA : IsSigmaCompact A) (hB : IsOpen B) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) A) :
    MeasurableSet {C : Fin d → α → ℂ | ∃ z ∈ A ∩ B, ∀ k, ∑ j, C k j * b j z = 0} := by
  obtain ⟨K, hK, hKA⟩ := hA
  have hBσ : IsSigmaCompact B := by
    haveI := hB.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨L, hL, hLB⟩ := hBσ
  have hEq : {C : Fin d → α → ℂ | ∃ z ∈ A ∩ B, ∀ k, ∑ j, C k j * b j z = 0} =
      ⋃ n, ⋃ m, {C : Fin d → α → ℂ | ∃ z ∈ K n ∩ L m, ∀ k, ∑ j, C k j * b j z = 0} := by
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨z, ⟨hzA, hzB⟩, h⟩
      rw [← hKA, Set.mem_iUnion] at hzA
      rw [← hLB, Set.mem_iUnion] at hzB
      obtain ⟨n, hn⟩ := hzA
      obtain ⟨m, hm⟩ := hzB
      exact ⟨n, m, z, ⟨hn, hm⟩, h⟩
    · rintro ⟨n, m, z, ⟨hn, hm⟩, h⟩
      refine ⟨z, ⟨?_, ?_⟩, h⟩
      · rw [← hKA]
        exact Set.mem_iUnion.mpr ⟨n, hn⟩
      · rw [← hLB]
        exact Set.mem_iUnion.mpr ⟨m, hm⟩
  rw [hEq]
  refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m => ?_
  refine (isClosed_meets_compact ((hK n).inter (hL m)) fun j => ?_).measurableSet
  refine (hb j).mono ?_
  intro z hz
  rw [← hKA]
  exact Set.mem_iUnion.mpr ⟨n, hz.1⟩

theorem natCast_le_encard_zeroSetIn_iff [T2Space X] [SecondCountableTopology X] (A : Set X)
    (b : α → X → ℂ) (C : Fin d → α → ℂ) (N : ℕ) :
    (N : ℕ∞) ≤ (zeroSetIn A b C).encard ↔
      ∃ f : Fin N → countableBasis X,
        (∀ i j, i ≠ j → Disjoint (f i : Set X) (f j)) ∧
        ∀ i, ∃ z ∈ A ∩ (f i : Set X), ∀ k, ∑ j, C k j * b j z = 0 := by
  classical
  constructor
  · intro hN
    obtain ⟨t, htZ, htN⟩ := Set.exists_subset_encard_eq hN
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htN
    haveI : Finite t := htfin.to_subtype
    have hcard : Nat.card t = N := by
      rw [Nat.card_coe_set_eq, Set.ncard_def, htN, ENat.toNat_natCast]
    let e : t ≃ Fin N := (Finite.equivFin t).trans (finCongr hcard)
    obtain ⟨U, hU, hdisj⟩ := htfin.t2_separation
    have hex : ∀ i : Fin N, ∃ v ∈ countableBasis X, (e.symm i : X) ∈ v ∧ v ⊆ U (e.symm i) :=
      fun i => (isBasis_countableBasis X).exists_subset_of_mem_open (hU _).1 (hU _).2
    choose v hvB hpv hvU using hex
    refine ⟨fun i => ⟨v i, hvB i⟩, ?_, ?_⟩
    · intro i j hij
      have hne : (e.symm i : X) ≠ e.symm j := by
        intro h
        exact hij (e.symm.injective (Subtype.ext h))
      show Disjoint (v i) (v j)
      exact Disjoint.mono (hvU i) (hvU j) (hdisj (e.symm i).2 (e.symm j).2 hne)
    · intro i
      have hz : (e.symm i : X) ∈ zeroSetIn A b C := htZ (e.symm i).2
      simp only [zeroSetIn, Set.mem_ofPred_eq] at hz
      exact ⟨e.symm i, ⟨hz.1, hpv i⟩, hz.2⟩
  · rintro ⟨f, hdisj, hz⟩
    choose z hzmem hzero using hz
    have hinj : Function.Injective z := by
      intro i j h
      by_contra hij
      have hzj : z i ∈ (f j : Set X) := by
        rw [h]
        exact (hzmem j).2
      exact Set.disjoint_left.mp (hdisj i j hij) (hzmem i).2 hzj
    have hsub : ((Finset.univ.image z : Finset X) : Set X) ⊆ zeroSetIn A b C := by
      intro x hx
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
      obtain ⟨i, rfl⟩ := hx
      simp only [zeroSetIn, Set.mem_ofPred_eq]
      exact ⟨(hzmem i).1, hzero i⟩
    calc (N : ℕ∞) = ((Finset.univ.image z : Finset X) : Set X).encard := by
          rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj,
            Finset.card_univ, Fintype.card_fin]
      _ ≤ (zeroSetIn A b C).encard := Set.encard_le_encard hsub

theorem measurableSet_natCast_le_encard_zeroSetIn [T2Space X] [SecondCountableTopology X]
    [LocallyCompactSpace X] {A : Set X} (hA : IsSigmaCompact A) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) A) (N : ℕ) :
    MeasurableSet {C : Fin d → α → ℂ | (N : ℕ∞) ≤ (zeroSetIn A b C).encard} := by
  classical
  haveI : Countable (countableBasis X) := (countable_countableBasis X).to_subtype
  have hEq : {C : Fin d → α → ℂ | (N : ℕ∞) ≤ (zeroSetIn A b C).encard} =
      ⋃ f : Fin N → countableBasis X, ⋃ (_ : ∀ i j, i ≠ j → Disjoint (f i : Set X) (f j)),
        ⋂ i, {C : Fin d → α → ℂ | ∃ z ∈ A ∩ (f i : Set X), ∀ k, ∑ j, C k j * b j z = 0} := by
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, exists_prop]
    exact natCast_le_encard_zeroSetIn_iff A b C N
  rw [hEq]
  refine MeasurableSet.iUnion fun f => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun i => ?_
  exact measurableSet_meets_inter hA ((isBasis_countableBasis X).isOpen (f i).2) hb

private theorem measurable_of_natCast_le_lemma {β : Type} [MeasurableSpace β] (g : β → ℕ∞)
    (hg : ∀ N : ℕ, MeasurableSet {x | (N : ℕ∞) ≤ g x}) : Measurable g := by
  refine measurable_to_countable' fun x => ?_
  induction x using ENat.recTopCoe with
  | top =>
    have h : g ⁻¹' {⊤} = ⋂ N : ℕ, {x | (N : ℕ∞) ≤ g x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      generalize g y = t
      induction t using ENat.recTopCoe with
      | top => exact ⟨fun _ _ => le_top, fun _ => rfl⟩
      | coe m =>
        constructor
        · intro hy
          exact absurd hy (ENat.natCast_ne_top m)
        · intro hy
          exfalso
          have h1 := hy (m + 1)
          norm_cast at h1
          omega
    rw [h]
    exact MeasurableSet.iInter hg
  | coe n =>
    have h : g ⁻¹' {(n : ℕ∞)} = {x | (n : ℕ∞) ≤ g x} \ {x | ((n + 1 : ℕ) : ℕ∞) ≤ g x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
      generalize g y = t
      induction t using ENat.recTopCoe with
      | top => simp
      | coe m =>
        norm_cast
        constructor
        · intro h1
          omega
        · intro h1
          omega
    rw [h]
    exact (hg n).diff (hg (n + 1))

theorem measurable_zeroCnt_of_continuousOn [T2Space X] [SecondCountableTopology X]
    [LocallyCompactSpace X] {A : Set X} (hA : IsSigmaCompact A) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) A) :
    Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by
  have hg : Measurable fun C : Fin d → α → ℂ => (zeroSetIn A b C).encard :=
    measurable_of_natCast_le_lemma _ fun N => measurableSet_natCast_le_encard_zeroSetIn hA hb N
  exact (Measurable.of_discrete (f := fun n : ℕ∞ => (n : ℝ≥0∞))).comp hg

theorem measurable_zeroCnt : ∀ (d : ℕ) (α : Type) [Fintype α] (U A : Set (V d)) (b : α → V d → ℂ),
    (∀ j, ContinuousOn (b j) U) → A ⊆ U → IsSigmaCompact A →
      Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by
  intro d α _ U A b hb hAU hA
  exact measurable_zeroCnt_of_continuousOn hA fun j => (hb j).mono hAU

end GlobalTheory.CompanionTheory.FSCrofton
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityReductionDiagonalProd
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.NuDiag

private theorem card_range_vecMul_mul_mul_eq_of_mul_eq_one {Q : Type} [CommRing Q] {n : ℕ}
    (H P P' G G' : Matrix (Fin n) (Fin n) Q) (hP : P' * P = 1) (hG : G * G' = 1) :
    Nat.card (Set.range fun z : Fin n → Q => Matrix.vecMul z (P * H * G)) =
      Nat.card (Set.range fun x : Fin n → Q => Matrix.vecMul x H) := by
  have hinj : Function.Injective fun y : Fin n → Q => Matrix.vecMul y G := by
    intro y₁ y₂ hy
    have h := congrArg (fun v => Matrix.vecMul v G') hy
    simpa only [Matrix.vecMul_vecMul, hG, Matrix.vecMul_one] using h
  have hrange : (Set.range fun z : Fin n → Q => Matrix.vecMul z (P * H * G)) =
      (fun y => Matrix.vecMul y G) '' Set.range fun x : Fin n → Q => Matrix.vecMul x H := by
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨Matrix.vecMul (Matrix.vecMul z P) H, ⟨Matrix.vecMul z P, rfl⟩,
        by simp only [Matrix.vecMul_vecMul]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨Matrix.vecMul x P', by
        simp only [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hP, Matrix.one_mul]⟩
  rw [hrange, Nat.card_image_of_injective hinj]

theorem cT_mul' {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (a b : Matrix (Fin n) (Fin n) R) :
    cT σ (a * b) = cT σ b * cT σ a := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one' {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} :
    cT σ (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem red_mul' {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} (a b : Matrix (Fin n) (Fin n) R) :
    red ϖ k (a * b) = red ϖ k a * red ϖ k b := by
  simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_mul]

theorem red_one' {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} :
    red ϖ k (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp only [PositivityTheory.PfSWUS.Loc.red]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem card_range_vecMul_diagonal {A : Type} [CommRing A] {n : ℕ} (e : Fin n → A) :
    Nat.card (Set.range fun z : Fin n → A => Matrix.vecMul z (Matrix.diagonal e)) =
      ∏ i : Fin n, Nat.card (Set.range fun w : A => w * e i) := by
  have hset : (Set.range fun z : Fin n → A => Matrix.vecMul z (Matrix.diagonal e)) =
      Set.pi Set.univ (fun i => Set.range fun w : A => w * e i) := by
    ext v
    simp only [Set.mem_range, Set.mem_univ_pi]
    constructor
    · rintro ⟨z, rfl⟩ i
      exact ⟨z i, by rw [Matrix.vecMul_diagonal]⟩
    · intro hv
      choose z hz using hv
      exact ⟨z, funext fun i => by rw [Matrix.vecMul_diagonal, hz i]⟩
  rw [hset, Nat.card_congr (Equiv.Set.univPi _), Nat.card_pi]

theorem nuAt_eq_prod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R), σ ϖ = ϖ → (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (n : ℕ) (h g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 → g' * g = 1 → cT σ g * h * g = Matrix.diagonal d → nuAt ϖ (red ϖ k h) = ∏ i : Fin n, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i)) := by
  intro R _ σ ϖ _ _ k _ n h g g' d hgg' hg'g hdiag
  have hP : PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g') *
      PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g) = 1 := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', ← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.cT_mul', hgg',
      GlobalTheory.CompanionTheory.SiegLoc.NuDiag.cT_one', GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_one']
  have hG : PositivityTheory.PfSWUS.Loc.red ϖ k g * PositivityTheory.PfSWUS.Loc.red ϖ k g' = 1 := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', hgg', GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_one']
  have hD : PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g) * PositivityTheory.PfSWUS.Loc.red ϖ k h *
      PositivityTheory.PfSWUS.Loc.red ϖ k g =
        Matrix.diagonal fun i => Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (d i) := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', ← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', hdiag]
    simp only [PositivityTheory.PfSWUS.Loc.red]
    exact Matrix.diagonal_map (map_zero _)
  unfold PositivityTheory.PfSWUS.Loc.nuAt
  refine Eq.trans ?_ (GlobalTheory.CompanionTheory.SiegLoc.NuDiag.card_range_vecMul_diagonal
    (fun i => Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (d i)))
  rw [← hD]
  exact (card_range_vecMul_mul_mul_eq_of_mul_eq_one _ _ _ _ _ hP hG).symm

end GlobalTheory.CompanionTheory.SiegLoc.NuDiag
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLawOfBlockDet
section
noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisPar

variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]

theorem continuous_circle_coe : Continuous (fun z : Circle => (z : ℂ)) := by
  first | fun_prop | exact continuous_subtype_val | exact continuous_induced_dom

theorem stab_univ_eq_top {κ : Type} [Fintype κ] [DecidableEq κ] : stab R (Set.univ : Set κ) = ⊤ := by
  refine eq_top_iff.2 fun g _ r hr => ?_
  exact absurd (Set.mem_univ r) hr

theorem isCh_of_top {G : Type} [Group G] [TopologicalSpace G] {Γ P : Subgroup G} {c : G → ℂ} (h : IsCh Γ ⊤ c) : IsCh Γ P c := by
  exact ⟨fun p _ q _ => h.mul p (Subgroup.mem_top p) q (Subgroup.mem_top q),
    fun p _ => h.norm p (Subgroup.mem_top p),
    fun γ hγ _ => h.rat γ hγ (Subgroup.mem_top γ),
    h.cont.mono fun x _ => Subgroup.mem_top x⟩

theorem isCh_cGL (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (κ : Type) [Fintype κ] [DecidableEq κ] :
    IsCh (A.ratGL κ) ⊤ (A.cGL κ) := by
  obtain ⟨-, hm, hcont, hr, -, hd⟩ := hB E R A hA κ Set.univ
  have htop : ∀ g : GL κ R, g ∈ stab R (Set.univ : Set κ) := fun g => by
    rw [stab_univ_eq_top]; trivial
  have hc : ∀ g : GL κ R, A.cGL κ g = A.χ (bdet Set.univ g) := fun g => by
    rw [hd]; rfl
  refine ⟨fun p _ q _ => ?_, fun p _ => ?_, fun γ hγ _ => ?_, ?_⟩
  · rw [hc, hc, hc, hm p (htop p) q (htop q), map_mul, Circle.coe_mul]
  · rw [hc]; exact Circle.norm_coe _
  · obtain ⟨x, hx⟩ := hr γ (htop γ) hγ
    rw [hc, hx, hA.χi, Circle.coe_one]
  · have hcon : Continuous (bdet (R := R) (Set.univ : Set κ)) := by
      rw [← continuousOn_univ]
      refine hcont.mono fun g _ => htop g
    have : A.cGL κ = fun g => ((A.χ (bdet Set.univ g) : Circle) : ℂ) := funext hc
    rw [this]
    exact (continuous_circle_coe.comp (hA.χcont.comp hcon)).continuousOn

theorem ext_gl (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (A : Ad E R) (hA : A.Good) (κ : Type) [Fintype κ] [DecidableEq κ]
    (t : Set κ) : IsHt (A.ratGL κ) (A.kGL κ) (stab R t) (A.htGL t) ∧
      ∀ p ∈ stab R t, ∀ k ∈ A.kGL κ, A.htGL t (p * k) = A.lg (bdet t p) := by
  obtain ⟨hc, hm, hcont, hr, hk, -⟩ := hB E R A hA.toGoodL κ t
  haveI : T2Space (GL κ R) := (hT E R A hA κ 1).1
  refine hE (GL κ R) (A.ratGL κ) (A.kGL κ) (stab R t) (fun p => A.lg (bdet t p)) (hA.kcpt κ) hc (hA.iwa κ t) ?_ ?_ hk ?_
  · intro p hp q hq
    simp only [hm p hp q hq, hA.lgmul]
  · exact hA.lgcont.comp_continuousOn hcont
  · intro p hp hg
    obtain ⟨x, hx⟩ := hr p hp hg
    simp only [hx, hA.lgi x]

theorem closed_uQ (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (ε : ℤˣ) {κ : Type} [Fintype κ] [DecidableEq κ] (t : Set κ) :
    IsClosed (A.uQ ε t : Set (A.U ε κ)) :=
  (hB E R A hA (κ ⊕ κ) (Sum.inl '' t)).1.preimage continuous_subtype_val

theorem ext_u (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (A : Ad E R) (hA : A.Good) (ε : ℤˣ) {κ : Type} [Fintype κ]
    [DecidableEq κ] (t : Set κ) (hI : Iwa (A.uQ ε t) (A.uK ε κ)) :
    IsHt (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε t) (A.uH ε t) ∧
      ∀ p ∈ A.uQ ε t, ∀ k ∈ A.uK ε κ, A.uH ε t (p * k) = A.lg (bdet (Sum.inl '' t) p.1) := by
  obtain ⟨-, hm, hcont, hr, hk, -⟩ := hB E R A hA.toGoodL (κ ⊕ κ) (Sum.inl '' t)
  obtain ⟨-, -, -, h2, -, -, hK⟩ := hT E R A hA κ ε
  haveI := h2
  refine hE (A.U ε κ) (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε t) (fun p => A.lg (bdet (Sum.inl '' t) p.1)) hK
    (closed_uQ hB A hA.toGoodL ε t) hI ?_ ?_ ?_ ?_
  · intro p hp q hq
    simp only [Subgroup.coe_mul, hm p.1 hp q.1 hq, hA.lgmul]
  · exact hA.lgcont.comp_continuousOn (hcont.comp continuous_subtype_val.continuousOn fun x hx => hx)
  · exact fun p hp hpk => hk p.1 hp hpk
  · intro p hp hg
    obtain ⟨x, hx⟩ := hr p.1 hp hg
    simp only [hx, hA.lgi x]

theorem isCh_uC (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (ε : ℤˣ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    IsCh (A.uΓ ε κ) (A.uQ ε (Set.univ : Set κ)) (A.uC ε κ) := by
  obtain ⟨-, hm, hcont, hr, -, -⟩ := hB E R A hA (κ ⊕ κ) (Sum.inl '' (Set.univ : Set κ))
  refine ⟨fun p hp q hq => ?_, fun p _ => Circle.norm_coe _, fun γ hγ hp => ?_, ?_⟩
  · simp only [Ad.uC, Subgroup.coe_mul, hm p.1 hp q.1 hq, map_mul, Circle.coe_mul]
  · obtain ⟨x, hx⟩ := hr γ.1 hp hγ
    simp only [Ad.uC, hx, hA.χi, Circle.coe_one]
  · exact continuous_circle_coe.comp_continuousOn
      (hA.χcont.comp_continuousOn (hcont.comp continuous_subtype_val.continuousOn fun x hx => hx))

theorem parLaw : BdetLaw → ExtLaw → GrpTop → ParLaw := by
  intro hB hE hT E R _ _ _ _ _ _ _ A hA ι _ _ ε s
  obtain ⟨hc, -⟩ := hB E R A hA.toGoodL ι s
  have hch := isCh_cGL hB A hA.toGoodL ι
  refine ⟨⟨⟨hc, hA.iwa ι s, ?_⟩, ⟨hc, hA.iwa ι s, isCh_of_top hch⟩, hch, (ext_gl hB hE hT A hA ι s).1, stab_univ_eq_top⟩, ?_⟩
  · refine ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => rfl, continuousOn_const⟩
  intro hI
  have hI' : Iwa (A.uQ ε s) (A.uK ε ι) := fun g => by
    obtain ⟨p, hp, k, hk, e⟩ := hI g
    exact ⟨p, hp.1, k, hk, e⟩
  have hu := ext_u hB hE hT A hA ε s hI'
  have hC := isCh_uC hB A hA.toGoodL (ε := ε) (κ := ι)
  refine ⟨⟨(closed_uQ hB A hA.toGoodL ε s).inter (closed_uQ hB A hA.toGoodL ε Set.univ), hI, ?_⟩, hu.1, fun g => ?_⟩
  · exact ⟨fun p hp q hq => hC.mul p hp.2 q hq.2, fun p hp => hC.norm p hp.2, fun γ hγ hp => hC.rat γ hγ hp.2,
      hC.cont.mono fun _ h => h.2⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := hI' g
    rw [hu.2 p hp k hk]
    exact ((ext_gl hB hE hT A hA (ι ⊕ ι) (Sum.inl '' s)).2 p.1 hp k.1 hk).symm

end GlobalTheory.CompanionTheory.RgEisPar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialIntegralMemSchwartzBruhat
section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

namespace GlobalTheory.CompanionTheory.TestFunctionFibreIntegral

theorem eventually_slice_eq {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (F : SB (A × B)) (a₀ : A) :
    ∀ᶠ a in nhds a₀, ∀ b, (F : A × B → ℂ) (a, b) = (F : A × B → ℂ) (a₀, b) := by
  obtain ⟨hF, hc⟩ := mem_SB_iff.1 F.2
  have hK : IsCompact (Prod.snd '' tsupport (F : A × B → ℂ)) := hc.isCompact.image continuous_snd
  have hopen : IsOpen {p : A × B | (F : A × B → ℂ) p = (F : A × B → ℂ) (a₀, p.2)} := by
    have h2 : IsLocallyConstant
        (fun p : A × B => (F : A × B → ℂ) p - (F : A × B → ℂ) (a₀, p.2)) :=
      hF.sub (hF.comp_continuous (by fun_prop))
    have h3 := h2.isOpen_fiber 0
    simpa [Set.preimage, sub_eq_zero] using h3
  obtain ⟨U, V, hU, -, haU, hKV, hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := a₀)) hK
    hopen (by
      rintro ⟨a, b⟩ ⟨ha, -⟩
      have ha' : a = a₀ := ha
      subst ha'
      rfl)
  filter_upwards [hU.mem_nhds (haU rfl)] with a ha b
  by_cases hb : b ∈ Prod.snd '' tsupport (F : A × B → ℂ)
  · exact hUV (Set.mk_mem_prod ha (hKV hb))
  · have h1 : (a, b) ∉ tsupport (F : A × B → ℂ) := fun h => hb ⟨_, h, rfl⟩
    have h2 : (a₀, b) ∉ tsupport (F : A × B → ℂ) := fun h => hb ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

theorem integral_mem_SB : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
    [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
    [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B] (μ : Measure B)
    [IsFiniteMeasureOnCompacts μ] (w : B → ℂ), Continuous w → ∀ F : SB (A × B),
    (fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) ∈ SB A := by
  intro A B _ _ _ _ _ _ _ _ _ _ μ _ w _ F
  obtain ⟨-, hc⟩ := mem_SB_iff.1 F.2
  refine mem_SB_iff.2 ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro a₀
    filter_upwards [eventually_slice_eq F a₀] with a ha
    simp only [ha]
  · refine HasCompactSupport.intro (hc.isCompact.image continuous_fst) ?_
    intro a ha
    have h0 : ∀ b, (F : A × B → ℂ) (a, b) = 0 := fun b =>
      image_eq_zero_of_notMem_tsupport fun h => ha ⟨_, h, rfl⟩
    simp only [h0, zero_mul, integral_zero]

end GlobalTheory.CompanionTheory.TestFunctionFibreIntegral
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionCorankEqRankLowerLeftStatement
section
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_corank_eq_rank_lower_left : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ (κ : GL (Ix n) O) (h : GL (Ix n) (IsLocalRing.ResidueField O)), IsRed (O := O) w κ h →
      iD h = (lowerLeftBlock (resK κ)).rank := by
  first | exact @GlobalTheory.CompanionTheory.Jp.RedRank.iD_eq_rank | exact GlobalTheory.CompanionTheory.Jp.RedRank.iD_eq_rank | (intros; apply GlobalTheory.CompanionTheory.Jp.RedRank.iD_eq_rank <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionUniqueUpToParabolicStatement
section
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_unique_up_to_parabolic : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (w : Lˣ) (κ : GL (Ix n) O) (h₁ h₂ : GL (Ix n) (IsLocalRing.ResidueField O)),
    IsRed (O := O) w κ h₁ → IsRed (O := O) w κ h₂ →
      ∃ (a d : GL (Fin n) (IsLocalRing.ResidueField O)) (b : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)),
        h₂ = pM a d b * h₁ := by
  first | exact @GlobalTheory.CompanionTheory.Jp.RedUnique.red_unique | exact GlobalTheory.CompanionTheory.Jp.RedUnique.red_unique | (intros; apply GlobalTheory.CompanionTheory.Jp.RedUnique.red_unique <;> assumption)
end

