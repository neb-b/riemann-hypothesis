module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoReline
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralMultilinear
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionRecursion
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0025
public import Development.WeilBound.CoreStatements.FlagImmersions.IntersectionSectionLogIntegral
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoEqRelinedIsometricVert
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.Swap

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem arList_swap_one {P : Ideal (MvPolynomial (Σ k, ι k) ℤ)}
    {I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) (T : LocPair ι ℤ Unit)
    (hT : T.IsVertOff P ∅) {A A' : HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A')
    (hiso : T.IsIsometric P (fun _ => A) (fun _ => A'))
    (pre post : List (HermLine ι)) (hpre : ∀ b ∈ pre, IsSmoothHerm b)
    (hpost : ∀ b ∈ post, IsSmoothHerm b) (hP : IsArithVar P ((pre ++ post).length + 1)) :
    arList I P (pre ++ A :: post) = arList I P (pre ++ A' :: post) := by
  have hL : ∀ j, IsSmoothHerm ((pre ++ post).get j) := fun j => by
    rcases List.mem_append.1 (List.get_mem _ j) with h | h
    · exact hpre _ h
    · exact hpost _ h
  have hsnoc : ∀ B : HermLine ι, IsSmoothHerm B → arList I P (pre ++ B :: post) =
      I P ((pre ++ post).length + 1) (Fin.snoc (pre ++ post).get B) := by
    intro B hB
    refine arList_eq_of_perm hP hI _ _ ?_ ?_
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using hB
      · simpa using hL i
    · rw [List.ofFn_succ']
      simp only [Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_get, List.concat_eq_append]
      exact List.perm_middle.trans (List.perm_append_singleton _ _).symm
  rw [hsnoc A hA, hsnoc A' hA']
  have h := _root_.GlobalTheory.CompanionTheory.Ar.Num.Link.change_line K ι P _ hP I hI ∅ T hT A A' hA hA' hiso (pre ++ post).get hL
  simpa [sub_eq_zero] using h

theorem arList_swap_map {J : Type} {P : Ideal (MvPolynomial (Σ k, ι k) ℤ)}
    {I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) (T : LocPair ι ℤ Unit)
    (hT : T.IsVertOff P ∅) {A A' : HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A')
    (hiso : T.IsIsometric P (fun _ => A) (fun _ => A')) (F G : J → HermLine ι)
    (hF : ∀ j, IsSmoothHerm (F j)) (hG : ∀ j, IsSmoothHerm (G j))
    (hFG : ∀ j, F j = G j ∨ (F j = A ∧ G j = A')) (l : List J) :
    ∀ (pre : List (HermLine ι)), (∀ b ∈ pre, IsSmoothHerm b) →
      IsArithVar P (pre.length + l.length) →
      arList I P (pre ++ l.map F) = arList I P (pre ++ l.map G) := by
  induction l with
  | nil => intro pre _ _; rfl
  | cons j l ih =>
    intro pre hpre hP
    have e1 : pre ++ (j :: l).map F = (pre ++ [F j]) ++ l.map F := by simp
    have e2 : (pre ++ [F j]) ++ l.map G = pre ++ F j :: l.map G := by simp
    have hpre' : ∀ b ∈ pre ++ [F j], IsSmoothHerm b := fun b hb => by
      rcases List.mem_append.1 hb with h | h
      · exact hpre b h
      · rw [List.mem_singleton.1 h]; exact hF j
    have hlen : (pre ++ [F j]).length + l.length = pre.length + (j :: l).length := by
      simp; omega
    rw [e1, ih _ hpre' (hlen ▸ hP), e2, List.map_cons]
    rcases hFG j with h | ⟨h, h'⟩
    · rw [h]
    · rw [h, h']
      refine arList_swap_one hI T hT hA hA' hiso pre _ hpre ?_ ?_
      · intro b hb
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
        exact hG i
      · have : (pre ++ l.map G).length + 1 = pre.length + (j :: l).length := by
          simp; omega
        exact this ▸ hP

theorem ofFn_monoLines {J : Type} (ℓ : J → HermLine ι) (m : J →₀ ℕ) (d : ℕ)
    (hd : (Finsupp.toMultiset m).toList.length = d) :
    List.ofFn (monoLines ℓ m d) = (Finsupp.toMultiset m).toList.map ℓ := by
  subst hd
  apply List.ext_get (by simp)
  intro n h₁ h₂
  simp [monoLines]

end GlobalTheory.CompanionTheory.Ar.Num.Swap

namespace GlobalTheory.CompanionTheory.Ar.Num.Link

open GlobalTheory.CompanionTheory.Ar.Top.Link

theorem arMono_swapA : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) [DecidableEq M.K] (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (A' : HermLine M.ι) (hs : IsSmoothHerm A') (hc : IsConjInvariantH A') (T : LocPair M.ι ℤ Unit), T.IsVertOff M.P ∅ → T.IsIsometric M.P (fun _ => M.A) (fun _ => A') → ∀ (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ), M.arMono II t m = (Link.reline M M.xdeg M.x M.x_deg M.x_smooth M.x_conj A' hs hc).arMono II t m := by
  intro Ψ _ N M _ II hII A' hs hc T hT hiso t m
  set M' := Link.reline M M.xdeg M.x M.x_deg M.x_smooth M.x_conj A' hs hc with hM'
  have hI : IsIntersectionFamily (II M.K M.ι) := hII.1 M.K M.ι
  have hP : IsArithVar M.P (dimFl Ψ N + 1) := M.arith
  have hF : ∀ j, IsSmoothHerm (M.line t j) := fun j => by
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  have hG : ∀ j, IsSmoothHerm (M'.line t j) := fun j => by
    cases j with
    | none => exact hs
    | some r => exact M.x_smooth t r
  have hFG : ∀ j, M.line t j = M'.line t j ∨ (M.line t j = M.A ∧ M'.line t j = A') := fun j => by
    cases j with
    | none => exact Or.inr ⟨rfl, rfl⟩
    | some r => exact Or.inl rfl
  show (if m.degree = dimFl Ψ N + 1 then
      II M.K M.ι M.P (dimFl Ψ N + 1) (monoLines (M.line t) m (dimFl Ψ N + 1)) /
        ((M.δ : ℝ) * (M.kA : ℝ) ^ m none) else 0) =
    (if m.degree = dimFl Ψ N + 1 then
      II M.K M.ι M.P (dimFl Ψ N + 1) (monoLines (M'.line t) m (dimFl Ψ N + 1)) /
        ((M.δ : ℝ) * (M.kA : ℝ) ^ m none) else 0)
  split_ifs with hd
  swap
  · rfl
  have hlen : (Finsupp.toMultiset m).toList.length = dimFl Ψ N + 1 := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hd]
    rfl
  have hmono : ∀ ℓ : Option (Ψ × Fin N) → HermLine M.ι, (∀ j, IsSmoothHerm (ℓ j)) →
      II M.K M.ι M.P (dimFl Ψ N + 1) (monoLines ℓ m (dimFl Ψ N + 1)) =
        arList (II M.K M.ι) M.P ((Finsupp.toMultiset m).toList.map ℓ) := by
    intro ℓ hℓ
    symm
    refine arList_eq_of_perm hP hI _ _ ?_ ?_
    · intro j
      unfold monoLines
      split_ifs with h
      · exact hℓ _
      · exact absurd (by have := j.2; omega) h
    · rw [Swap.ofFn_monoLines ℓ m _ hlen]
  have key : arList (II M.K M.ι) M.P ((Finsupp.toMultiset m).toList.map (M.line t)) =
      arList (II M.K M.ι) M.P ((Finsupp.toMultiset m).toList.map (M'.line t)) :=
    Swap.arList_swap_map hI T hT M.A_smooth hs hiso _ _ hF hG hFG _ [] (by simp) (by simpa [hlen] using hP)
  exact congrArg (· / ((M.δ : ℝ) * (M.kA : ℝ) ^ m none))
    ((hmono _ hF).trans (key.trans (hmono (M'.line t) hG).symm))

end GlobalTheory.CompanionTheory.Ar.Num.Link
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionBound
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem effective_mul_nef_nonneg : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : Ω), IsArithVar (mCoordIdeal y) (e + 2) → Birational y → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → s ≠ 0 → s ∈ chartLatNm y A.a 1 → (∀ j W', IsArithVar W' 2 → mCoordIdeal y ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral (mCoordIdeal y) (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) :=
  @RootFieldNumerics.intersection_section_log_integral

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightBoundOfArithVar
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem rootLines_vert_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (x x' : CMType H × Fin (D.p + D.q) → K → ℤ) (e₀ e : CMType H × Fin (D.p + D.q) → Ω), (Fl.shrink S₀ h hvb hsub).RootLines x e₀ → Fl.RootLines x' e → ∃ f g : CMType H × Fin (D.p + D.q) → MvPolynomial (Σ k, J k) ℤ, (∀ r, aeval y (f r) = e r / e₀ r * aeval y (g r)) ∧ (⟨x, x', f, g⟩ : LocPair J ℤ (CMType H × Fin (D.p + D.q))).IsVertOff (mCoordIdeal y) ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d ha Fl S₀ h hvb hsub x x' e₀ e h₀ h₁
  have key : ∀ r, ∃ f g : MvPolynomial (Σ k, J k) ℤ,
      (⟨fun _ => x r, fun _ => x' r, fun _ => f, fun _ => g⟩ : LocPair J ℤ Unit).IsVertOff (mCoordIdeal y)
        ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧
      aeval y f = e r / e₀ r * aeval y g := by
    intro r
    refine _root_.GlobalTheory.CompanionTheory.Ar.Num.lat_vertOff 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie d ha ((Fl.shrink S₀ h hvb hsub).rootLat r) (Fl.rootLat r)
      (x r) (x' r) (e₀ r) (e r) (h₀ r) (h₁ r) _ ?_
    intro q hq
    exact _root_.GlobalTheory.CompanionTheory.Ar.Num.rootLat_shrink_eq E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha Fl S₀ h hvb hsub q
      (fun p hp hp' hf => hq ⟨p, 𝔐.S_prime p hp⟩ (Finset.mem_preimage.2 (Finset.mem_sdiff.2 ⟨hp, hp'⟩)) hf) r
  choose f g hv hr using key
  exact ⟨f, g, hr, fun r => hv r ()⟩

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginHeightComparisonTwo
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Top.LineUnit

section Pull

variable {K₀ : Type} [Fintype K₀] {ι₀ : K₀ → Type} [∀ k, Fintype (ι₀ k)] {Ω₀ : Type} [Field Ω₀]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

theorem rename_mem_mCoordIdeal {y₀ : (Σ k, ι₀ k) → Ω₀} {y : (Σ k, J k) → Ω} {κ : K₀ → K}
    {v : (Σ k, ι₀ k) → Σ k, J k} (i : Ω₀ →+* Ω) (hv : ∀ p, (v p).1 = κ p.1)
    (hy : ∀ p, y (v p) = i (y₀ p)) {f : MRing ι₀} (hf : f ∈ mCoordIdeal y₀) :
    rename v f ∈ mCoordIdeal y := by
  let ψ : MvPolynomial K₀ Ω₀ →+* MvPolynomial K Ω := eval₂Hom (C.comp i) fun k => X (κ k)
  have e : (mConeMap y).toRingHom.comp (rename v : MRing ι₀ →ₐ[ℤ] MRing J).toRingHom =
      ψ.comp (mConeMap y₀).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun p => ?_
    · simp
    · simp [mConeMap, ψ, hy, hv]
  have h0 : mConeMap y₀ f = 0 := hf
  show mConeMap y (rename v f) = 0
  have := congrArg (fun φ => φ f) e
  simpa [h0] using this

theorem pull_mem_mcPts {y₀ : (Σ k, ι₀ k) → Ω₀} {y : (Σ k, J k) → Ω} {κ : K₀ → K}
    {v : (Σ k, ι₀ k) → Σ k, J k} (i : Ω₀ →+* Ω) (hb : IsBlockMap κ v)
    (hy : ∀ p, y (v p) = i (y₀ p)) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    (fun p => z (v p)) ∈ mcPts (mCoordIdeal y₀) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨j, hj⟩ := hz.1 (κ k)
    obtain ⟨p, hp⟩ := hb.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩
    have h2 : p.1 = k := hb.1 (by rw [← hb.2.2.1 p, hp])
    obtain ⟨pk, pi⟩ := p
    simp only at h2
    subst h2
    refine ⟨pi, ?_⟩
    show z (v ⟨pk, pi⟩) ≠ 0
    rw [hp]
    exact hj
  · have := hz.2 _ (rename_mem_mCoordIdeal i hb.2.2.1 hy hf)
    rwa [map_rename, eval_rename] at this

theorem X_mem_mCoordIdeal_iff (y : (Σ k, J k) → Ω) (q : Σ k, J k) :
    (X q : MRing J) ∈ mCoordIdeal y ↔ y q = 0 := by
  show mConeMap y (X q) = 0 ↔ _
  simp [mConeMap, X_ne_zero]

theorem block_onto {κ : K₀ → K} {v : (Σ k, ι₀ k) → Σ k, J k} (hb : IsBlockMap κ v) {n : Type}
    (k₀ : K₀) (e : n ≃ ι₀ k₀) (q : Σ k, J k) (hq : q.1 = κ k₀) : ∃ i, v ⟨k₀, e i⟩ = q := by
  obtain ⟨p, hp⟩ := hb.2.2.2 q ⟨k₀, hq.symm⟩
  have h2 : p.1 = k₀ := hb.1 (by rw [← hb.2.2.1 p, hp, hq])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨e.symm pi, by simpa using hp⟩

theorem pullDeg_single [DecidableEq K] {κ : K₀ → K} (hκ : Function.Injective κ) {a : K₀ → ℤ} {k₀ : K₀}
    (h1 : a k₀ = 1) (h2 : ∀ k, k ≠ k₀ → a k = 0) :
    pullDeg κ a = fun k => (((Pi.single (κ k₀) 1 : K → ℕ) k : ℕ) : ℤ) := by
  funext k'
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [pullDeg, hκ.extend_apply]
    by_cases e : k = k₀
    · subst e
      simp [h1]
    · have : κ k ≠ κ k₀ := fun h => e (hκ h)
      simp [h2 k e, this]
  · rw [pullDeg, Function.extend_apply' _ _ _ hk]
    have : k' ≠ κ k₀ := fun h => hk ⟨k₀, h.symm⟩
    simp [this]

end Pull

section Minors

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  {y : (Σ k, J k) → Ω} {n : Type} {w₀ w₁ : n → Σ k, J k} {a₀ a₁ : K}

theorem minor_mem (b₀ : ∀ i, (w₀ i).1 = a₀) (b₁ : ∀ i, (w₁ i).1 = a₁)
    (hw : ∀ i, y (w₀ i) = y (w₁ i)) (i j : n) :
    (X (w₀ i) * X (w₁ j) - X (w₀ j) * X (w₁ i) : MRing J) ∈ mCoordIdeal y := by
  show mConeMap y _ = 0
  simp only [mConeMap, map_sub, map_mul, aeval_X, b₀, b₁, hw]
  ring

theorem exists_unit [DecidableEq K] (b₀ : ∀ i, (w₀ i).1 = a₀) (b₁ : ∀ i, (w₁ i).1 = a₁)
    (s₀ : ∀ q : Σ k, J k, q.1 = a₀ → ∃ i, w₀ i = q) (s₁ : ∀ q : Σ k, J k, q.1 = a₁ → ∃ i, w₁ i = q)
    (hw : ∀ i, y (w₀ i) = y (w₁ i)) (a : n) {W : Ideal (MRing J)} (hW : W.IsPrime)
    (hPW : mCoordIdeal y ≤ W) (hrel : GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W) :
    ∃ u v : MRing J, u ∉ W ∧ v ∉ W ∧ u * X (w₀ a) - v * X (w₁ a) ∈ mCoordIdeal y := by
  obtain ⟨i, hi⟩ := hrel a₀
  obtain ⟨b, hb⟩ := s₀ ⟨a₀, i⟩ rfl
  obtain ⟨j, hj⟩ := hrel a₁
  obtain ⟨c, hc⟩ := s₁ ⟨a₁, j⟩ rfl
  rw [← hb] at hi
  rw [← hc] at hj
  have hu : (X (w₁ b) : MRing J) ∉ W := by
    intro h
    have m := hPW (minor_mem b₀ b₁ hw b c)
    have h2 : (X (w₀ b) * X (w₁ c) : MRing J) ∈ W := by
      have := W.add_mem m (W.mul_mem_left (X (w₀ c)) h)
      simpa using this
    exact (hW.mem_or_mem h2).elim hi hj
  refine ⟨X (w₁ b), X (w₀ b), hu, hi, ?_⟩
  have e : (X (w₁ b) * X (w₀ a) - X (w₀ b) * X (w₁ a) : MRing J) =
      X (w₀ a) * X (w₁ b) - X (w₀ b) * X (w₁ a) := by ring
  rw [e]
  exact minor_mem b₀ b₁ hw a b

theorem exists_prop (b₀ : ∀ i, (w₀ i).1 = a₀) (b₁ : ∀ i, (w₁ i).1 = a₁)
    (s₀ : ∀ q : Σ k, J k, q.1 = a₀ → ∃ i, w₀ i = q) (s₁ : ∀ q : Σ k, J k, q.1 = a₁ → ∃ i, w₁ i = q)
    (hw : ∀ i, y (w₀ i) = y (w₁ i)) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ r : ℂ, r ≠ 0 ∧ ∀ i, z (w₀ i) = r * z (w₁ i) := by
  obtain ⟨i, hi⟩ := hz.1 a₀
  obtain ⟨b, hb⟩ := s₀ ⟨a₀, i⟩ rfl
  obtain ⟨j, hj⟩ := hz.1 a₁
  obtain ⟨c, hc⟩ := s₁ ⟨a₁, j⟩ rfl
  rw [← hb] at hi
  rw [← hc] at hj
  have hm : ∀ i j, z (w₀ i) * z (w₁ j) = z (w₀ j) * z (w₁ i) := fun i j => by
    have := hz.2 _ (minor_mem b₀ b₁ hw i j)
    simpa [sub_eq_zero] using this
  have h0 : z (w₀ c) ≠ 0 := fun h => by
    have := hm b c
    rw [h, zero_mul] at this
    exact mul_ne_zero hi hj this
  refine ⟨z (w₀ c) / z (w₁ c), div_ne_zero h0 hj, fun i => ?_⟩
  have := hm i c
  field_simp
  exact this

end Minors

section Origin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem hf_smul {Y : Model Xo c β} {S : Finset ℕ} {M : RootModel (CMType H) (D.p + D.q)}
    {Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}
    (o : RootOrigin Y S M Fx) {z : (Σ k, M.ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal M.y)) {r : ℂ} (hr : r ≠ 0) :
    Fx.hf (fun i => r * z ⟨o.k₀, o.ix i⟩) = ‖r‖ * Fx.hf fun i => z ⟨o.k₀, o.ix i⟩ := by
  classical
  let cc : M.K → ℂ := fun k => if k = o.k₀ then r else 1
  have hcc : ∀ k, cc k ≠ 0 := fun k => by
    by_cases e : k = o.k₀ <;> simp [cc, e, hr]
  have hz' := mcPts_smul M.arith.2.1.2.1 cc hcc hz
  have e1 := o.A_h _ hz'
  have e2 := M.A.smul cc z hcc
  have e3 := o.A_h _ hz
  have e4 : (∏ k, ‖cc k‖ ^ M.A.a k) = ‖r‖ := by
    rw [Finset.prod_eq_single o.k₀]
    · simp [cc, o.A_deg.1]
    · intro k _ hk
      simp [o.A_deg.2 k hk]
    · simp
  have e5 : cc o.k₀ = r := by simp [cc]
  rw [e4, e3] at e2
  rw [← e2, e1]
  simp only [e5]

end Origin

end GlobalTheory.CompanionTheory.Ar.Top.LineUnit

namespace GlobalTheory.CompanionTheory.Ar.Top.LineUnit

theorem lines_isometric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (M₀ M₁ : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o₀ : RootOrigin Y S₀ M₀ Fx) (o₁ : RootOrigin Y S M₁ Fx) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (κ₀ : M₀.K → K) (v₀ : (Σ k, M₀.ι k) → Σ k, J k) (κ₁ : M₁.K → K) (v₁ : (Σ k, M₁.ι k) → Σ k, J k) (i₀ : M₀.Ω →+* Ω) (i₁ : M₁.Ω →+* Ω) (h₀ : IsBlockMap κ₀ v₀) (h₁ : IsBlockMap κ₁ v₁), (∀ p, y (v₀ p) = i₀ (M₀.y p)) → (∀ p, y (v₁ p) = i₁ (M₁.y p)) → i₀.comp o₀.g = i₁.comp o₁.g → IsArithVar (mCoordIdeal y) (dimFl (CMType H) (D.p + D.q) + 1) → ∃ T : LocPair J ℤ Unit, T.x () = (pullHerm h₀ M₀.A).a ∧ T.x' () = (pullHerm h₁ M₁.A).a ∧ T.IsVertOff (mCoordIdeal y) ∅ ∧ T.IsIsometric (mCoordIdeal y) (fun _ => pullHerm h₀ M₀.A) (fun _ => pullHerm h₁ M₁.A) := by
  intro E _ _ _ H D l Xo c Y S₀ S M₀ M₁ Sys Fx o₀ o₁ Ω _ K _ _ J _ y κ₀ v₀ κ₁ v₁ i₀ i₁ h₀ h₁ hy₀ hy₁ hg ha
  let w₀ : Fin (Fx.m + 1) → Σ k, J k := fun i => v₀ ⟨o₀.k₀, o₀.ix i⟩
  let w₁ : Fin (Fx.m + 1) → Σ k, J k := fun i => v₁ ⟨o₁.k₀, o₁.ix i⟩
  have b₀ : ∀ i, (w₀ i).1 = κ₀ o₀.k₀ := fun i => h₀.2.2.1 _
  have b₁ : ∀ i, (w₁ i).1 = κ₁ o₁.k₀ := fun i => h₁.2.2.1 _
  have s₀ : ∀ q : Σ k, J k, q.1 = κ₀ o₀.k₀ → ∃ i, w₀ i = q := block_onto h₀ o₀.k₀ o₀.ix
  have s₁ : ∀ q : Σ k, J k, q.1 = κ₁ o₁.k₀ → ∃ i, w₁ i = q := block_onto h₁ o₁.k₀ o₁.ix
  have hw : ∀ i, y (w₀ i) = y (w₁ i) := fun i => by
    have e := congrArg (fun φ => φ (Fx.yf i)) hg
    simp only [RingHom.comp_apply] at e
    show y (v₀ _) = y (v₁ _)
    rw [hy₀, hy₁, o₀.y_eq, o₁.y_eq]
    exact e
  obtain ⟨j, hj⟩ := ha.2.1.2.2 (κ₀ o₀.k₀)
  obtain ⟨a, ha'⟩ := s₀ ⟨κ₀ o₀.k₀, j⟩ rfl
  rw [← ha'] at hj
  have hf : (X (w₀ a) : MRing J) ∉ mCoordIdeal y := hj
  have hg' : (X (w₁ a) : MRing J) ∉ mCoordIdeal y := by
    rw [X_mem_mCoordIdeal_iff, ← hw, ← X_mem_mCoordIdeal_iff]
    exact hf
  have d₀ : (pullHerm h₀ M₀.A).a = fun k => (((Pi.single (κ₀ o₀.k₀) 1 : K → ℕ) k : ℕ) : ℤ) :=
    pullDeg_single h₀.1 o₀.A_deg.1 o₀.A_deg.2
  have d₁ : (pullHerm h₁ M₁.A).a = fun k => (((Pi.single (κ₁ o₁.k₀) 1 : K → ℕ) k : ℕ) : ℤ) :=
    pullDeg_single h₁.1 o₁.A_deg.1 o₁.A_deg.2
  have hX : ∀ (q : Σ k, J k) (k : K), q.1 = k →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (X q : MRing J) (Pi.single k 1) := by
    rintro q k rfl
    exact isWeightedHomogeneous_X ℤ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight J) q
  refine ⟨⟨fun _ => (pullHerm h₀ M₀.A).a, fun _ => (pullHerm h₁ M₁.A).a,
    fun _ => X (w₀ a), fun _ => X (w₁ a)⟩, rfl, rfl, fun _ => ⟨?_, hf, hg', ?_⟩, fun _ => ⟨rfl, rfl, ?_⟩⟩
  · refine ⟨Pi.single (κ₀ o₀.k₀) 1, Pi.single (κ₁ o₁.k₀) 1, hX _ _ (b₀ a), hX _ _ (b₁ a), ?_⟩
    show _ = (pullHerm h₀ M₀.A).a - (pullHerm h₁ M₁.A).a
    rw [d₀, d₁]
    rfl
  · intro W hW hPW hrel _
    exact exists_unit b₀ b₁ s₀ s₁ hw a hW hPW hrel
  · intro z hz
    obtain ⟨r, hr, hp⟩ := exists_prop b₀ b₁ s₀ s₁ hw hz
    have z₀ := pull_mem_mcPts i₀ h₀ hy₀ hz
    have z₁ := pull_mem_mcPts i₁ h₁ hy₁ hz
    have e₀ := o₀.A_h _ z₀
    have e₁ := o₁.A_h _ z₁
    have es := hf_smul o₁ z₁ hr
    have hfun : (fun i => z (w₀ i)) = fun i => r * z (w₁ i) := funext hp
    show ‖eval z (map (Int.castRingHom ℂ) (X (w₀ a)))‖ * M₁.A.h (fun p => z (v₁ p)) =
      ‖eval z (map (Int.castRingHom ℂ) (X (w₁ a)))‖ * M₀.A.h (fun p => z (v₀ p))
    rw [map_X, map_X, eval_X, eval_X, e₀, e₁]
    have e₂ : Fx.hf (fun i => z (v₀ ⟨o₀.k₀, o₀.ix i⟩)) = ‖r‖ * Fx.hf (fun i => z (v₁ ⟨o₁.k₀, o₁.ix i⟩)) := by
      rw [← es]
      exact congrArg Fx.hf hfun
    rw [e₂, hp a, norm_mul]
    ring

end GlobalTheory.CompanionTheory.Ar.Top.LineUnit
end

