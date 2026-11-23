module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0067
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0052
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0054

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleWeightAntisymmetricEq
section
open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.SegmentWords

theorem wt_inSh_antisymm : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L M : List (ASeg T)), AOrdered s L →
    AOrdered s M → InSh s (M : Multiset (ASeg T)) (wt s L) →
    InSh s (L : Multiset (ASeg T)) (wt s M) →
    (L : Multiset (ASeg T)) = (M : Multiset (ASeg T)) := by
  intro T s hs hj L M hL hM hLM hML
  by_contra hne
  have h1 := GlobalTheory.T.shuffle_weight_square_length_lt s hs hj L (M : Multiset (ASeg T)) hL hLM (Ne.symm hne)
  have h2 := GlobalTheory.T.shuffle_weight_square_length_lt s hs hj M (L : Multiset (ASeg T)) hM hML hne
  exact lt_asymm h1 h2

end GlobalTheory.CompanionTheory.SegmentWords
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelInductionFromGallery
section
noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEis

section Heights

variable {G : Type} [Group G] [TopologicalSpace G]

theorem isHt_mono {Γ K P P' : Subgroup G} {η : G → ℝ} (h : IsHt Γ K P η) (hP : P' ≤ P) : IsHt Γ K P' η :=
  ⟨fun p hp g => h.left p (hP hp) g, h.right, fun γ hγ hp => h.rat γ hγ (hP hp), h.cont⟩

theorem isHt_lin {Γ K P : Subgroup G} {η θ : G → ℝ} (x y : ℝ) (h₁ : IsHt Γ K P η) (h₂ : IsHt Γ K P θ) :
    IsHt Γ K P fun g => x * η g + y * θ g := by
  refine ⟨?_, ?_, ?_, (continuous_const.mul h₁.cont).add (continuous_const.mul h₂.cont)⟩
  · intro p hp g
    simp only [h₁.left p hp g, h₂.left p hp g]
    ring
  · intro g k hk
    simp only [h₁.right g k hk, h₂.right g k hk]
  · intro γ hγ hp
    simp only [h₁.rat γ hγ hp, h₂.rat γ hγ hp, mul_zero, add_zero]

theorem isHt_congr {Γ K P : Subgroup G} {η θ : G → ℝ} (h : IsHt Γ K P η) (e : ∀ g, θ g = η g) : IsHt Γ K P θ := by
  rwa [show θ = η from funext e]

theorem conv_congr {Γ P : Subgroup G} {l l' : G → ℝ} (h : Conv Γ P l) (e : ∀ g, l' g = l g) : Conv Γ P l' := by
  rwa [show l' = l from funext e]

end Heights

variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]


open scoped Classical in
theorem wallQ (hTr : Transfer) (hTop : GrpTop) (hPar : ParLaw) (hLQ : LeviQ) (A : Ad E R) (hA : A.Good) (ε : ℤˣ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : Set ι) (hI : Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι))
    (hSg : A.Sg ε (sᶜ : Set ι)) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (ρ : A.uK ε ι →* (W →L[ℂ] W)) (hρ : Continuous ρ) :
    HasWall (A.uΓ ε ι ⊓ A.uQ ε s) (A.uK ε ι) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uC ε ι)
      (fun g => A.uH ε Set.univ g - A.uH ε s g) (fun g => A.uH ε Set.univ g - A.uH ε s g)
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * (A.uH ε Set.univ g - A.uH ε s g)) ρ := by
  obtain ⟨π, j, c₀, hL, hP, hIw, hPH⟩ := hLQ E R A hA ι ε s hI
  obtain ⟨-, -, -, t₄, t₅, -, t₇⟩ := hTop E R A hA ι ε
  obtain ⟨-, -, -, u₄, u₅, -, u₇⟩ := hTop E R A hA (sᶜ : Set ι) ε
  have hP' := (hPar E R A hA (sᶜ : Set ι) ε Set.univ).2 (by rwa [inf_idem])
  rw [inf_idem] at hP'
  obtain ⟨hp, hh, -⟩ := hP'
  have hβ' : IsHt (A.uΓ ε (sᶜ : Set ι)) (A.uK ε (sᶜ : Set ι)) (A.uQ ε Set.univ)
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * A.uH ε Set.univ g) :=
    isHt_congr (isHt_lin (Fintype.card (sᶜ : Set ι) : ℝ) 0 hh hh) fun g => by ring
  have hPβ : PullHt (A.uK ε ι) (A.uQ ε s) π
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * (A.uH ε Set.univ g - A.uH ε s g))
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * A.uH ε Set.univ g) := by
    intro q k hk
    have := hPH q k hk
    simp only at this ⊢
    rw [this]
  exact (hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j c₀ _ _ _ _ _ _ _ _ _ _ 0 u₇ hL hP hP hP hp hp hp hh hh hβ'
    hPH hPH hPβ hPH).1 (hSg hIw)

theorem wallsS (hTr : Transfer) (hTw : Twist) (hTop : GrpTop) (hPar : ParLaw) (hLS : LeviS) (A : Ad E R) (hA : A.Good)
    (hMir : A.MirGL) (ε : ℤˣ) {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ i₁ : ι) (hN : 2 ≤ Fintype.card ι)
    (hS : Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι)) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : A.uK ε ι →* (W →L[ℂ] W)) (hρ : Continuous ρ) :
    HasFirst (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε {i₀}) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)) ρ ∧
    HasWall (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uC ε ι) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g) (A.uH ε {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.uH ε {i₀} g - A.uH ε Set.univ g) ρ ∧
    HasLast (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε {i₀}) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g))
      (A.uH ε Set.univ) (Fintype.card ι) ρ := by
  obtain ⟨π, j, hL, hP, -, hH⟩ := hLS E R A hA ι ε hS
  obtain ⟨g₁, g₂, -, t₄, t₅, -, t₇⟩ := hTop E R A hA ι ε
  have hk := hA.kcpt ι
  obtain ⟨a₁, a₂, ch, h₀, -⟩ := (hPar E R A hA ι ε {i₀}).1
  obtain ⟨b₁, b₂, -, h₁, -⟩ := (hPar E R A hA ι ε {i₁}ᶜ).1
  obtain ⟨u₁, u₂, -, hu, hst⟩ := (hPar E R A hA ι ε Set.univ).1
  rw [hst] at u₁ u₂ hu
  have hPS : IsPull (A.uQ ε Set.univ) (A.uQ ε Set.univ) ⊤ π 1 (A.uC ε ι) (A.cGL ι) := by
    have := hP Set.univ
    rwa [inf_idem, hst] at this
  have e : (1 : GL ι R → ℂ) * A.cGL ι = A.cGL ι := one_mul _
  obtain ⟨m₁, m₂, m₃⟩ := hMir ι i₀ i₁ hN
  have d₁ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ) (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) :=
    isHt_congr (isHt_lin 1 (-1) h₁ (isHt_mono hu le_top)) fun g => by ring
  have d₂ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ)
      (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) :=
    isHt_congr (isHt_lin (Fintype.card ι : ℝ) (1 - (Fintype.card ι : ℝ)) h₁ (isHt_mono hu le_top)) fun g => by ring
  have d₃ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) :=
    isHt_congr (isHt_lin (Fintype.card ι : ℝ) (-1) h₀ (isHt_mono hu le_top)) fun g => by ring
  have p₁ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) := by
    intro q k hk'
    simp only [hH {i₁}ᶜ q k hk', hH Set.univ q k hk']
  have p₂ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g))
      (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) := by
    intro q k hk'
    simp only [hH {i₁}ᶜ q k hk', hH Set.univ q k hk']
  have p₃ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π
      (fun g => (Fintype.card ι : ℝ) * A.uH ε {i₀} g - A.uH ε Set.univ g)
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) := by
    intro q k hk'
    simp only [hH {i₀} q k hk', hH Set.univ q k hk']
  have T₁ := hTw (GL ι R) (A.ratGL ι) (A.kGL ι) ⊤ (stab R {i₀}) (stab R {i₁}ᶜ) 1 (A.cGL ι) (A.htGL {i₀})
    (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g)
    (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) (A.htGL Set.univ)
    (Fintype.card ι) hk ch u₁ a₁ b₁
  have T₂ := hTw (GL ι R) (A.ratGL ι) (A.kGL ι) ⊤ (stab R {i₁}ᶜ) (stab R {i₀}) 1 (A.cGL ι)
    (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) (A.htGL {i₀})
    (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) (A.htGL Set.univ)
    (Fintype.card ι) hk ch u₁ b₁ a₁
  rw [e] at T₁ T₂
  have X₁ := hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j 1 _ _ _ _ _ _ _ _ _ _ (Fintype.card ι) hk hL hPS
    (hP {i₀}) (hP {i₁}ᶜ) u₂ a₂ b₂ h₀ d₁ d₂ (hH {i₀}) p₁ p₂ (hH Set.univ)
  have X₂ := hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j 1 _ _ _ _ _ _ _ _ _ _ (Fintype.card ι) hk hL hPS
    (hP {i₁}ᶜ) (hP {i₀}) u₂ b₂ a₂ d₁ h₀ d₃ p₁ (hH {i₀}) p₃ (hH Set.univ)
  exact ⟨X₁.2.1 (T₁.2.1 m₁), X₂.1 (T₂.1 m₂), X₁.2.2 (T₁.2.2 m₃)⟩


open Classical in
theorem sgStep : Gallery → Transfer → Twist → GrpTop → ParLaw → LeviS → LeviQ → ConvGrOf → ConvU → SgStep := by
  classical
  intro hGal hTr hTw hTop hPar hLS hLQ hCG hCU E R _ _ _ _ _ _ _ A hA hMir ε ι _ _ hN hIH hS W _ _ _ ρ hρ
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨π, j, -, -, hIw, -⟩ := hLS E R A hA ι ε hS
  obtain ⟨-, -, -, t₄, t₅, t₆, t₇⟩ := hTop E R A hA ι ε
  obtain ⟨Ra, ca₁, ca₂⟩ := hCU E R A hA (hCG E R A hA hMir) ι ε {i₀} (hIw _)
  obtain ⟨Rb, -, cb₂⟩ := hCU E R A hA (hCG E R A hA hMir) ι ε {i₀}ᶜ (hIw _)
  have pS := (hPar E R A hA ι ε Set.univ).2 (hIw _)
  rw [inf_idem] at pS
  have pA := (hPar E R A hA ι ε {i₀}).2 (hIw _)
  have pB := (hPar E R A hA ι ε {i₀}ᶜ).2 (hIw _)
  have hc₀ : ∀ f : Fintype ({i₀}ᶜ : Set ι), @Fintype.card _ f = Fintype.card ι - 1 := fun f => by
    rw [Fintype.card_compl_set]; simp
  have hc₁ : ∀ f : Fintype (({i₀}ᶜ : Set ι)ᶜ : Set ι), @Fintype.card _ f = 1 := fun f => by
    rw [Fintype.card_compl_set, hc₀]; omega
  have hc₀' : ∀ f : Fintype ({i₀}ᶜ : Set ι), ((@Fintype.card _ f : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := fun f => by
    rw [hc₀, Nat.cast_sub (by omega)]; simp
  have hq := fun (s : Set ι) (f : Fintype (sᶜ : Set ι)) (d : DecidableEq (sᶜ : Set ι)) => @hIH (sᶜ : Set ι) f d
  have w₁ := wallQ hTr hTop hPar hLQ A hA ε {i₀} (hIw _)
    (hq _ _ _ (by rw [hc₀]; omega) (by rw [hc₀]; omega)) ρ hρ
  have w₂ := wallQ hTr hTop hPar hLQ A hA ε {i₀}ᶜ (hIw _)
    (hq _ _ _ (hc₁ _).ge (by rw [hc₁]; omega)) ρ hρ
  rw [hc₀'] at w₁
  rw [hc₁] at w₂
  simp only [Nat.cast_one, one_mul] at w₂
  rw [show (fun g => A.uH ε Set.univ g - A.uH ε {i₀}ᶜ g) = fun g => -(A.uH ε {i₀}ᶜ g - A.uH ε Set.univ g) from
    funext fun g => by ring] at w₂
  obtain ⟨s₁, s₂, s₃⟩ := wallsS hTr hTw hTop hPar hLS A hA hMir ε i₀ i₀ hN hS ρ hρ
  refine hGal (A.U ε ι) W (A.uK ε ι) ρ t₇ hρ inferInstance (A.uΓ ε ι) (A.uQ ε Set.univ)
    (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀}ᶜ ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀}) (A.uQ ε {i₀}ᶜ) (A.uC ε ι)
    (A.uH ε Set.univ) (A.uH ε {i₀}) (fun g => A.uH ε {i₀}ᶜ g - A.uH ε Set.univ g) (Fintype.card ι)
    inf_le_right inf_le_right inf_le_left inf_le_left pS.1 pA.1 pB.1 pS.2.1 pA.2.1
    (isHt_congr pB.2.1 fun g => by ring) ⟨max Ra Rb, fun y hy => ca₁ y (lt_of_le_of_lt (le_max_left _ _) hy),
      fun z y hz hy => ca₂ z y (lt_of_le_of_lt (le_max_left _ _) hz) (lt_of_le_of_lt (le_max_left _ _) hy),
      fun r y hr hy => conv_congr (cb₂ r y (lt_of_le_of_lt (le_max_right _ _) hr)
        (lt_of_le_of_lt (le_max_right _ _) hy)) fun g => by ring⟩ s₁ w₂ s₂ w₁ s₃

end GlobalTheory.CompanionTheory.RgEis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaCompactDisjointRefinement
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.CroftonPartition

theorem isSigmaCompact_of_isOpen_compact {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] {U : Set X} (hU : IsOpen U) : IsSigmaCompact U := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance

theorem isSigmaCompact_inter_isClosed {X : Type} [TopologicalSpace X] {s C : Set X}
    (hs : IsSigmaCompact s) (hC : IsClosed C) : IsSigmaCompact (s ∩ C) := by
  obtain ⟨K, hK, hKs⟩ := hs
  refine ⟨fun n => K n ∩ C, fun n => (hK n).inter_right hC, ?_⟩
  rw [← hKs, Set.iUnion_inter]

theorem exists_sigmaCompact_partition : ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] (ι : Type) (S : ι → Set X), (∀ i, IsOpen (S i)) →
    (⋃ i, S i) = Set.univ → ∃ (m : ℕ) (l : Fin m → ι) (A : Fin m → Set X),
      Pairwise (Function.onFun Disjoint A) ∧ (⋃ t, A t) = Set.univ ∧ (∀ t, A t ⊆ S (l t)) ∧
      ∀ t, IsSigmaCompact (A t) := by
  intro X _ _ _ _ ι S hS hcov
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover S hS hcov.ge
  let e := t.equivFin
  let l : Fin t.card → ι := fun j => (e.symm j : ι)
  let A : Fin t.card → Set X := fun j => S (l j) \ ⋃ (i : Fin t.card) (_ : i < j), S (l i)
  refine ⟨t.card, l, A, ?_, ?_, ?_, ?_⟩
  · intro j j' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact Set.disjoint_left.2 fun x hx hx' => hx'.2 (Set.mem_iUnion₂.2 ⟨j, h, hx.1⟩)
    · exact Set.disjoint_left.2 fun x hx hx' => hx.2 (Set.mem_iUnion₂.2 ⟨j', h, hx'.1⟩)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    have hl : l (e ⟨i, hit⟩) = i := by simp [l]
    obtain ⟨j, hj, hmin⟩ := wellFounded_lt.has_min {j : Fin t.card | x ∈ S (l j)}
      ⟨e ⟨i, hit⟩, by simpa [hl] using hxi⟩
    refine Set.mem_iUnion.2 ⟨j, hj, fun hx => ?_⟩
    obtain ⟨i', hi', hxi'⟩ := Set.mem_iUnion₂.1 hx
    exact hmin i' hxi' hi'
  · intro j
    exact Set.sdiff_subset
  · intro j
    show IsSigmaCompact (S (l j) \ ⋃ (i : Fin t.card) (_ : i < j), S (l i))
    rw [Set.sdiff_eq]
    exact isSigmaCompact_inter_isClosed (isSigmaCompact_of_isOpen_compact (hS _))
      (isClosed_compl_iff.2 (isOpen_iUnion fun i => isOpen_iUnion fun _ => hS _))

end GlobalTheory.CompanionTheory.CroftonPartition
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardEtaleLocalSection
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.EtaleSection

theorem exists_sub_mem_of_prod_mem {S B : Type} [CommRing S] [CommRing B] [Algebra S B]
    (Q : Ideal B) (hQ : Q.IsPrime) (x : B) (s : Multiset S)
    (h : (s.map fun b => x - algebraMap S B b).prod ∈ Q) :
    ∃ b ∈ s, x - algebraMap S B b ∈ Q := by
  induction s using Multiset.induction_on with
  | empty =>
    exact absurd ((Ideal.eq_top_iff_one Q).2 (by simpa using h)) hQ.ne_top
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons] at h
    rcases hQ.mem_or_mem h with h | h
    · exact ⟨a, Multiset.mem_cons_self a s, h⟩
    · obtain ⟨b, hb, hbQ⟩ := ih h
      exact ⟨b, Multiset.mem_cons_of_mem hb, hbQ⟩

theorem exists_section_standardEtale : ∀ {S : Type} [CommRing S] , Aic (S := S) → Loc (S := S) →
    ∀ (B : Type) [CommRing B] [Algebra S B] [Algebra.IsStandardEtale S B] (Q : Ideal B), Q.IsPrime →
    (Q.comap (algebraMap S B)).IsMaximal →
    ∃ e : S, IsIdempotentElem e ∧ e ∉ Q.comap (algebraMap S B) ∧
      Nonempty (B →ₐ[S] Localization.Away e) := by
  intro S _ hA hL B _ _ _ Q hQ hm
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := S) (S := B)
  obtain ⟨s, hs⟩ := GlobalTheory.T.absolutely_closed_polynomial_splits hA P.f P.monic_f

  have hprod : (s.map fun b => P.x - algebraMap S B b).prod ∈ Q := by
    have h0 : Polynomial.aeval P.x P.f = 0 := P.hasMap.1
    rw [hs, map_multiset_prod, Multiset.map_map] at h0
    have : (s.map fun b => P.x - algebraMap S B b).prod = 0 := by
      rw [← h0]
      congr 1
      apply Multiset.map_congr rfl
      intro b _
      simp
    rw [this]
    exact Q.zero_mem
  obtain ⟨b, hbs, hbQ⟩ := exists_sub_mem_of_prod_mem Q hQ P.x s hprod
  have hroot : Polynomial.eval b P.f = 0 := by
    have hd : (Polynomial.X - Polynomial.C b) ∣ P.f := by
      rw [hs]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hbs)
    exact Polynomial.dvd_iff_isRoot.1 hd

  set c : S := Polynomial.eval b P.g with hc
  have hcm : c ∉ Q.comap (algebraMap S B) := by
    intro hcQ
    have hcQ' : algebraMap S B c ∈ Q := hcQ
    have hd : P.x - algebraMap S B b ∣
        Polynomial.aeval P.x P.g - algebraMap S B c := by
      have := Polynomial.sub_dvd_eval_sub P.x (algebraMap S B b) (P.g.map (algebraMap S B))
      rwa [Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at this
    have hgQ : Polynomial.aeval P.x P.g ∈ Q := by
      have h1 := Ideal.mem_of_dvd Q hd hbQ
      simpa using Q.add_mem h1 hcQ'
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hgQ P.hasMap.2)

  obtain ⟨a, μ, hμ, haμ⟩ := hm.exists_inv hcm
  obtain ⟨e, he, hec, he1⟩ := hL (a * c)
  have h1ac : 1 - a * c = μ := by rw [← haμ]; ring
  have he1m : 1 - e ∈ Q.comap (algebraMap S B) := by
    rw [h1ac] at he1
    exact (Ideal.span_singleton_le_iff_mem _).2 hμ he1
  have hem : e ∉ Q.comap (algebraMap S B) := by
    intro hem
    have : (1 : S) ∈ Q.comap (algebraMap S B) := by
      simpa using Ideal.add_mem _ hem he1m
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine ⟨e, he, hem, ?_⟩

  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hec
  have heu : IsUnit (algebraMap S (Localization.Away e) e) :=
    IsLocalization.Away.algebraMap_isUnit e
  have hcu : IsUnit (algebraMap S (Localization.Away e) c) := by
    have : algebraMap S (Localization.Away e) e =
        algebraMap S (Localization.Away e) (r * a) * algebraMap S (Localization.Away e) c := by
      rw [← map_mul, ← hr]; ring_nf
    rw [this] at heu
    exact isUnit_of_mul_isUnit_right heu
  have hmap : P.P.HasMap (algebraMap S (Localization.Away e) b) := by
    refine ⟨?_, ?_⟩
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hroot, map_zero]
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      exact hcu
  exact ⟨(P.P.lift _ hmap).comp P.equivRing.toAlgHom⟩

end GlobalTheory.CompanionTheory.EtaleSection
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformHorizontalInvariance
section
noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem shiftFst_bound {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ l : ℂ × ℂ, l.1.re ∈ Set.Icc a b → l.2.re = c →
      ‖Complex.exp (-dot l t) • G l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  have hC : IsCompact ((fun s : ℝ => (s, c)) '' Set.Icc a b) :=
    isCompact_Icc.image (Continuous.prodMk continuous_id continuous_const)
  have hCΩ : (fun s : ℝ => (s, c)) '' Set.Icc a b ⊆ Ω := by
    rintro _ ⟨s, hs', rfl⟩
    exact hs s hs'
  obtain ⟨M₀, hM₀⟩ := hG.3 _ hCΩ hC
  refine ⟨Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) * |M₀|, by positivity, ?_⟩
  intro l hl hlc
  have hmem : l ∈ PositivityTheory.RgEis.tube ((fun s : ℝ => (s, c)) '' Set.Icc a b) := by
    show (l.1.re, l.2.re) ∈ (fun s : ℝ => (s, c)) '' Set.Icc a b
    exact ⟨l.1.re, hl, Prod.ext rfl hlc.symm⟩
  have hGl := hM₀ l hmem
  have hre : (-GlobalTheory.CompanionTheory.TubeFourier.dot l t).re = -(l.1.re * t.1 + l.2.re * t.2) := by
    simp [GlobalTheory.CompanionTheory.TubeFourier.dot]
  have hx : |l.1.re| ≤ |a| + |b| :=
    abs_le.2 ⟨by linarith [neg_abs_le a, abs_nonneg b, hl.1], by linarith [le_abs_self b, abs_nonneg a, hl.2]⟩
  have hexp : ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot l t)‖ ≤
      Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) := by
    rw [Complex.norm_exp, hre, hlc]
    apply Real.exp_le_exp.2
    have e1 : -(l.1.re * t.1) ≤ (|a| + |b|) * |t.1| := by
      calc -(l.1.re * t.1) ≤ |l.1.re * t.1| := neg_le_abs _
        _ = |l.1.re| * |t.1| := abs_mul _ _
        _ ≤ (|a| + |b|) * |t.1| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have e2 : -(c * t.2) ≤ |c| * |t.2| := by
      rw [← abs_mul]
      exact neg_le_abs _
    linarith
  rw [norm_smul]
  calc ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot l t)‖ * ‖G l‖
      ≤ Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) *
          (|M₀| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))) :=
        mul_le_mul hexp (hGl.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le))
          (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) * |M₀| *
          Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by ring

theorem integrable_exp_neg_sq_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
  have h := (integrable_exp_neg_mul_sq one_pos).mul_prod (integrable_exp_neg_mul_sq one_pos)
  rw [← MeasureTheory.Measure.volume_eq_prod] at h
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [neg_mul, one_mul]

theorem shiftFst_integrable {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) {s : ℝ} (hsm : s ∈ Set.Icc a b) :
    Integrable (fun y : ℝ × ℝ => Complex.exp (-dot (pt (s, c) y) t) • G (pt (s, c) y)) := by
  obtain ⟨M, -, hM⟩ := GlobalTheory.CompanionTheory.TubeFourier.shiftFst_bound hG hs t
  have htp : Continuous (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c)) := by
    have h : GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) = fun y : ℝ × ℝ =>
        ((s : ℂ) + (y.1 : ℂ) * Complex.I, (c : ℂ) + (y.2 : ℂ) * Complex.I) := by
      funext y
      simp only [GlobalTheory.CompanionTheory.TubeFourier.pt, Complex.mk_eq_add_mul_I]
    rw [h]
    fun_prop
  have hmem : ∀ y, GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y ∈ PositivityTheory.RgEis.tube Ω := fun _ => hs s hsm
  have hGc : Continuous (fun y => G (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y)) := hG.2.comp_continuous htp hmem
  have hpair : Continuous (fun l : ℂ × ℂ => GlobalTheory.CompanionTheory.TubeFourier.dot l t) := by
    simp only [GlobalTheory.CompanionTheory.TubeFourier.dot]
    fun_prop
  have hE : Continuous (fun y => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) t)) :=
    (hpair.comp htp).neg.cexp
  refine MeasureTheory.Integrable.mono'
    (GlobalTheory.CompanionTheory.TubeFourier.integrable_exp_neg_sq_prod.const_mul M)
    (hE.smul hGc).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  refine (hM (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) hsm rfl).trans (le_of_eq ?_)
  show M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) = M * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2))
  rw [← Real.exp_add]
  congr 2
  ring

theorem phi_eq_iterated {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) {s : ℝ} (hsm : s ∈ Set.Icc a b) :
    phi G (s, c) t = ∫ y₂ : ℝ, ∫ y₁ : ℝ,
      Complex.exp (-dot (pt (s, c) (y₁, y₂)) t) • G (pt (s, c) (y₁, y₂)) := by
  have h := shiftFst_integrable hG hs t hsm
  unfold phi
  rw [Measure.volume_eq_prod] at h ⊢
  exact integral_prod_symm _ h

end GlobalTheory.CompanionTheory.TubeFourier

theorem GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst :
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X),
      GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) →
        ∀ t : ℝ × ℝ, phi G (a, c) t = phi G (b, c) t := by
  intro X _ _ _ Ω G hG a b c hab hs t
  rw [GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated hG hs t (Set.left_mem_Icc.2 hab),
    GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated hG hs t (Set.right_mem_Icc.2 hab)]
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.CompanionTheory.TubeFourier.shiftFst_bound hG hs t
  refine integral_congr_ae (ae_of_all _ fun y₂ => ?_)
  have hline : DifferentiableOn ℂ (fun z : ℂ => G (z, ⟨c, y₂⟩)) {z : ℂ | z.re ∈ Set.Icc a b} := by
    have h1 := hG.1 ((0 : ℂ), (⟨c, y₂⟩ : ℂ)) ((1 : ℂ), (0 : ℂ))
    have heq : ∀ τ : ℂ, ((0 : ℂ), (⟨c, y₂⟩ : ℂ)) + τ • ((1 : ℂ), (0 : ℂ)) = (τ, ⟨c, y₂⟩) :=
      fun τ => Prod.ext (by simp) (by simp)
    simp only [heq] at h1
    refine h1.mono fun z hz => ?_
    exact hs z.re hz
  have hpair : Differentiable ℂ (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t)) := by
    simp only [GlobalTheory.CompanionTheory.TubeFourier.dot]
    fun_prop
  have hdiff : DifferentiableOn ℂ
      (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩))
      {z : ℂ | z.re ∈ Set.Icc a b} :=
    hpair.differentiableOn.smul hline
  have hbound : ∀ z : ℂ, z.re ∈ Set.Icc a b →
      ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩)‖ ≤
        M * Real.exp (-z.im ^ 2) := by
    intro z hz
    refine (hM (z, ⟨c, y₂⟩) hz rfl).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM0)
    show -(z.im ^ 2 + y₂ ^ 2) ≤ -z.im ^ 2
    linarith [sq_nonneg y₂]
  exact _root_.GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line X
    (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩))
    a b M hab hdiff hbound
end
end

