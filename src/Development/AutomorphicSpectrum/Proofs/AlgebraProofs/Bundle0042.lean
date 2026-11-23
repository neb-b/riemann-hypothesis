module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentValuationFibre
public import Development.WeilBound.CoreStatements.HodgeTatePoints.BilinearPartAx3
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0040
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0024
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0017
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPluckerFrame
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValuationLatticeMatrixReduction

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagFrameBaseExtension
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullFlagFrame

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)

theorem tri_solve {F : Type} [Field F] {N : ℕ} (T : Fin N → Fin N → F) (a : Fin N → F)
    (hT : ∀ j l, j < l → T j l = 0) (hd : ∀ j, T j j ≠ 0) (i : Fin N)
    (h : ∀ l, i < l → ∑ j, a j * T j l = 0) : ∀ j, i < j → a j = 0 := by
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨j₀, hj₀, ha₀⟩ := hne
  let S := Finset.univ.filter (fun j => i < j ∧ a j ≠ 0)
  have hS : S.Nonempty := ⟨j₀, by simp [S, hj₀, ha₀]⟩
  have hm : S.max' hS ∈ S := S.max'_mem hS
  obtain ⟨m, hmd⟩ : ∃ m, m = S.max' hS := ⟨_, rfl⟩
  rw [← hmd] at hm
  have hm' : i < m ∧ a m ≠ 0 := by simpa [S] using hm
  have hsum := h m hm'.1
  rw [Finset.sum_eq_single m] at hsum
  · exact mul_ne_zero hm'.2 (hd m) hsum
  · intro j _ hjm
    rcases lt_or_gt_of_ne hjm with hlt | hgt
    · rw [hT j m hlt, mul_zero]
    · have hz : a j = 0 := by
        by_contra hz
        have hjS : j ∈ S := by simp [S, hz, hm'.1.trans hgt]
        have := S.le_max' j hjS
        rw [← hmd] at this
        exact absurd this (not_le.2 hgt)
      rw [hz, zero_mul]
  · simp

section BC

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω₁ : Type} [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem mseg_bcCoord (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (bcCoord x z) s =
      algebraMap Ω Ω₁ (mseg x (restrictChart s)) * ∏ k, z ⟨k, s (.inr k)⟩ := by
  simp [mseg, Fintype.prod_sum_type, bcCoord, joinCoord, restrictChart, map_prod]

theorem map_mem_chartRing_bc (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (bcCoord x z) s ≠ 0) {a : Ω}
    (ha : a ∈ chartRing O (mseg x) (restrictChart s)) :
    algebraMap Ω Ω₁ a ∈ chartRing O (mseg (bcCoord x z)) s := by
  have hZ : (∏ k, z ⟨k, s (.inr k)⟩) ≠ 0 := by
    intro h0
    exact hs (by rw [mseg_bcCoord, h0, mul_zero])
  induction ha using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨j, rfl⟩ := ht
    let j' : ∀ k : K ⊕ K', Sum.elim ι ι' k := fun k =>
      match k with
      | .inl k => j k
      | .inr k => s (.inr k)
    have hj : restrictChart j' = j := rfl
    have hz : (∏ k, z ⟨k, j' (.inr k)⟩) = ∏ k, z ⟨k, s (.inr k)⟩ := rfl
    have e : algebraMap Ω Ω₁ (mseg x j / mseg x (restrictChart s)) =
        mseg (bcCoord x z) j' / mseg (bcCoord x z) s := by
      rw [mseg_bcCoord, mseg_bcCoord, hj, hz, map_div₀, mul_div_mul_right _ _ hZ]
    rw [e]
    exact Algebra.subset_adjoin ⟨j', rfl⟩
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply O Ω Ω₁]
    exact Subalgebra.algebraMap_mem _ r
  | add s t _ _ hs ht => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hs ht
  | mul s t _ _ hs ht => rw [map_mul]; exact Subalgebra.mul_mem _ hs ht

variable {N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]
  {V₁ : Type} [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]

theorem repr_bc (bc : V →ₗ[Ω] V₁) (w : Module.Basis (Fin N) Ω V) (w₁ : Module.Basis (Fin N) Ω₁ V₁)
    (hw : ∀ i, w₁ i = bc (w i)) (e : V) (j : Fin N) :
    w₁.repr (bc e) j = algebraMap Ω Ω₁ (w.repr e j) := by
  have h1 : bc e = ∑ i, algebraMap Ω Ω₁ (w.repr e i) • w₁ i := by
    conv_lhs => rw [← w.sum_repr e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hw, algebraMap_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
      mul_one]
  · intro i _ hij
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg hij,
      smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem isFlagFrame_bc (x : (Σ k, ι k) → Ω) (E : ChartBundle O (mseg x) N V)
    (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ) (h : IsFlagFrame x E w b)
    (z : (Σ k, ι' k) → Ω₁) (bc : V →ₗ[Ω] V₁) (w₁ : Module.Basis (Fin N) Ω₁ V₁)
    (hw : ∀ i, w₁ i = bc (w i)) (EB : ChartBundle O (mseg (bcCoord x z)) N V₁)
    (hp : IsPullBC O x z bc E EB) :
    IsFlagFrame (bcCoord x z) EB w₁ (fun i => pullDeg (K' := K') (b i)) := by
  classical
  refine ⟨fun s hs0 i => ?_⟩
  have hs : mseg (bcCoord x z) s ≠ 0 := hs0
  have hc : mseg x (restrictChart s) ≠ 0 := by
    intro h0
    exact hs (by rw [mseg_bcCoord, h0, map_zero, zero_mul])
  obtain ⟨u, hu, hup, hdiag, hgen⟩ :=
    FlagPairExt.exists_frame x E w b h (restrictChart s) hc
  have hx : ∀ k, x ⟨k, restrictChart s k⟩ ≠ 0 := fun k =>
    (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ k)
  have hM : ∀ i, (∏ k, x ⟨k, restrictChart s k⟩ ^ b i k) ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  have hMon : (∏ k : K ⊕ K', (bcCoord x z) ⟨k, s k⟩ ^ pullDeg (K' := K') (b i) k) =
      algebraMap Ω Ω₁ (∏ k, x ⟨k, restrictChart s k⟩ ^ b i k) := by
    rw [Fintype.prod_sum_type]
    simp [pullDeg, bcCoord, joinCoord, restrictChart, map_prod, map_zpow₀]
  have hbu : ∀ j, bc (u j) ∈ EB.lat s := by
    intro j
    rw [hp s hs]
    exact AddSubgroup.subset_closure ⟨1, Subalgebra.one_mem _, u j, hu j, (one_smul _ _).symm⟩
  have hgenL : ∀ v ∈ EB.lat s, ∃ a : Fin N → Ω₁,
      (∀ j, a j ∈ chartRing O (mseg (bcCoord x z)) s) ∧ v = ∑ j, a j • bc (u j) := by
    intro v hv
    rw [hp s hs] at hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨a, ha, e, he, rfl⟩ := hv
      obtain ⟨t, ht, rfl⟩ := hgen e he
      refine ⟨fun j => a * algebraMap Ω Ω₁ (t j), fun j =>
        Subalgebra.mul_mem _ ha (map_mem_chartRing_bc x z s hs (ht j)), ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← algebraMap_smul Ω₁ (t j), smul_smul]
    | zero => exact ⟨0, fun _ => Subalgebra.zero_mem _, by simp⟩
    | add v v' _ _ hv hv' =>
      obtain ⟨a, ha, rfl⟩ := hv
      obtain ⟨a', ha', rfl⟩ := hv'
      exact ⟨a + a', fun j => Subalgebra.add_mem _ (ha j) (ha' j), by
        simp [add_smul, Finset.sum_add_distrib]⟩
    | neg v _ hv =>
      obtain ⟨a, ha, rfl⟩ := hv
      exact ⟨-a, fun j => Subalgebra.neg_mem _ (ha j), by simp [Finset.sum_neg_distrib]⟩
  ext t
  constructor
  · rintro ⟨v, hv, htri, rfl⟩
    obtain ⟨a, ha, hav⟩ := hgenL v hv
    let T : Fin N → Fin N → Ω₁ := fun j l => algebraMap Ω Ω₁ (w.repr (u j) l)
    have hrepr : ∀ l, w₁.repr v l = ∑ j, a j * T j l := by
      intro l
      rw [hav]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [T, map_sum, repr_bc bc w w₁ hw]
    have hT : ∀ j l, j < l → T j l = 0 := fun j l hjl => by simp [T, hup j l hjl]
    have hd : ∀ j, T j j ≠ 0 := fun j => by
      simp only [T, hdiag j]
      exact (map_ne_zero _).2 (hM j)
    have hz := tri_solve T a hT hd i fun l hl => by rw [← hrepr l]; exact htri l hl
    refine ⟨a i, ha i, ?_⟩
    rw [hrepr i, Finset.sum_eq_single i]
    · show a i * T i i = _
      rw [hMon]
      simp only [T, hdiag i]
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · rw [hT j i hlt, mul_zero]
      · rw [hz j hgt, zero_mul]
    · simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a • bc (u i), EB.stable s a ha _ (hbu i), fun j hj => ?_, ?_⟩
    · simp [repr_bc bc w w₁ hw, hup i j hj]
    · rw [hMon]
      simp [repr_bc bc w w₁ hw, hdiag i]

end BC

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V) (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsFlagFrame (joinCoord x z) EB w (fun i => pullDeg (K' := K') (b i))) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁) (w₁ : Module.Basis (Fin N) Ω₁ V₁), (∀ i, w₁ i = bc (w i)) → ∀ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB → IsFlagFrame (bcCoord x z) EB w₁ (fun i => pullDeg (K' := K') (b i)) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E w b h
  refine ⟨?_, ?_⟩
  · intro K' _ _ ι' _ z EB hp
    exact isFlagFrame_bc (Ω₁ := Ω) (V₁ := V) x E w b h z LinearMap.id w (fun _ => rfl) EB hp
  · intro Ω₁ _ _ _ _ K' _ _ ι' _ z V₁ _ _ _ _ bc w₁ hw EB hp
    exact isFlagFrame_bc x E w b h z bc w₁ hw EB hp

end GlobalTheory.CompanionTheory.Ar.Num.PullFlagFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalHermitianActionPairing
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem rhoH_hom_adjoint : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), (∃ ρH : O →+* Module.End R ((Fin d → R) × (Fin d → R)), ∀ a, ρH a = rhoH B a) ∧ (bil B.sy 1 1).transpose = - bil B.sy 1 1 ∧ ∀ a y y', pairH B (rhoH B a y) y' = pairH B y (rhoH B (star a) y') :=
  @PositivityTheory.HtPt.Ca.rhoH_hom

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransport
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.Iso

theorem rho_pairing : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d), IsIso B B₂ φ ψ lam → lin φ 1 * lin ψ 1 = 1 ∧ lin ψ 1 * lin φ 1 = 1 ∧ Function.Bijective (transH φ ψ lam) ∧ (∀ a, rho B a * lin φ 1 = lin φ 1 * rho B₂ a) ∧ (∀ a, rhoH B a ∘ₗ transH φ ψ lam = transH φ ψ lam ∘ₗ rhoH B₂ a) ∧ ∀ y y', pairH B (transH φ ψ lam y) (transH φ ψ lam y') = pairH B₂ y y' :=
  PositivityTheory.HtPt.Ca.iso_rho

end GlobalTheory.CompanionTheory.Ar.Conj.Iso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractElementaryStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_retract_elementary : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary | exact GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary | (intros; apply GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MultiProjectivePrimeIntersectionStatement
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multi_projective_prime_intersection : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d r : ℕ, 0 < r → IsModelOver (pointIdeal O x) d → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (W : Ideal (MRing (Sum.elim ι ι') O)), IsMultiProjPrime W → pointIdeal O (joinCoord x z) ≤ W → (C ϖ : MRing (Sum.elim ι ι') O) ∈ W → ∀ l : List (K → ℤ), l.length = d + r → ringKrullDim (MRing (Sum.elim ι ι') O ⧸ W) ≤ ((d + r + Fintype.card (K ⊕ K') : ℕ) : WithBot ℕ∞) → vNumL W (l.map (pullDeg (K' := K'))) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.vNumL_pull_eq_zero_of_contracted | exact GlobalTheory.CompanionTheory.Ar.Num.vNumL_pull_eq_zero_of_contracted | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.vNumL_pull_eq_zero_of_contracted <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RootFundamentalWeightDuality
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem rootOnFund_mul_fundOnRoot_inverse : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (r r' : Ψ × Fin N), (∑ a, rootOnFund r a * fundOnRoot a r' = if r = r' then 1 else 0) ∧ (∀ π : Ψ ≃ Ψ, rootOnFund (π r.1, r.2) (π r'.1, r'.2) = rootOnFund r r' ∧ fundOnRoot (π r.1, r.2) (π r'.1, r'.2) = fundOnRoot r r') :=
  @PositivityTheory.UnitarySelfGeneration.h_fundinv

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBundleChain
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.CommonFlag

theorem exists_basis_mem {O Ω τ V : Type} [CommRing O] [Field Ω] [Algebra O Ω] [AddCommGroup V]
    [Module Ω V] {N : ℕ} {y : τ → Ω} (B : ChartBundle O y N V) {c : τ} (hc : y c ≠ 0) :
    ∃ w : Module.Basis (Fin N) Ω V, ∀ i, w i ∈ B.lat c := by
  classical
  obtain ⟨k, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hsum
  obtain ⟨b, hli, hsp, hiff⟩ := hb l
  have hbl : ∀ q, ∃ n : ℕ, f l ^ n • b q ∈ B.lat c := fun q =>
    (hiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by by_cases h : q' = q <;> simp [h]⟩,
      by simp [Pi.single_apply]⟩
  choose n hn using hbl
  refine ⟨(Module.Basis.mk hli hsp.ge).unitsSMul fun q => Units.mk0 (f l ^ n q) (pow_ne_zero _ hl),
    fun q => ?_⟩
  rw [Module.Basis.unitsSMul_apply, Module.Basis.mk_apply]
  exact hn q

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N n : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : Fin (n + 1) → ChartBundle O (mseg x) N V), (∀ j, SameGeneric O x (E 0) (E j)) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω) (EB : Fin (n + 1) → ChartBundle O (mseg (joinCoord x z)) N V) (w : Module.Basis (Fin N) Ω V) (b : Fin (n + 1) → Fin N → K ⊕ K' → ℤ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ fnField O (joinCoord x z) = fnField O x ∧ ∀ j, IsPull O x z (E j) (EB j) ∧ IsFlagFrame (joinCoord x z) (EB j) w (b j) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hx N n V _ _ E hE
  obtain ⟨hK, hx0, hinj, hT⟩ := (PositivityTheory.Xgn.A_join_model.isModelOver_iff x d).1 hx
  choose s₀ hs₀ using hx0
  have hs : mseg x s₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hs₀ k
  obtain ⟨w, hw⟩ := exists_basis_mem (E 0) hs
  have hgen : ∀ j, ∃ (a : K → ℤ) (M : ℕ) (φ : Fin M → Module.Dual Ω V),
      IsTwistedDualGens x (E j) a φ := fun j => by
    obtain ⟨a, ha⟩ := TwistedDualGensExist.proof O Ω K ι x N V (E j)
    exact ⟨a, ha a le_rfl⟩
  choose a M φ hφ using hgen
  obtain ⟨hz, hfn⟩ := GlobalTheory.CompanionTheory.Ar.Num.plucker_birat O Ω K ι x N V (Fin (n + 1)) E M a φ hφ w s₀ hs
  have hfn' := hfn fun j i => by
    obtain ⟨c, hc, hcw⟩ := (hE j s₀ hs).1 (w i) (hw i)
    exact ⟨c, (map_ne_zero_iff _ hinj).2 hc, hcw⟩
  have hpull : ∀ j, ∃ EB : ChartBundle O (mseg (joinCoord x (pluckerCoord φ w))) N V,
      IsPull O x (pluckerCoord φ w) (E j) EB := fun j =>
    (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V (E j)).1 _ _ (pluckerCoord φ w)
  choose EB hEB using hpull
  refine ⟨Fin (n + 1) × Fin (N + 1), inferInstance, inferInstance, pluckerIdx N M, inferInstance,
    pluckerCoord φ w, EB, w, fun j => pluckerDeg (a j) j, ?_, hfn', fun j => ⟨hEB j,
      PositivityTheory.Xgn.t_plucker_frame O Ω K ι x N V (Fin (n + 1)) E M a φ hφ w j (EB j) (hEB j)⟩⟩
  refine (PositivityTheory.Xgn.A_join_model.isModelOver_iff _ d).2 ⟨inferInstance, ?_, hinj, ?_⟩
  · rintro (k | k)
    · exact ⟨s₀ k, hs₀ k⟩
    · exact hz k
  · rw [hfn', hT]

end GlobalTheory.CompanionTheory.Ar.CommonFlag
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalIdealStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_fundamental_ideal : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → (∀ χ : MulChar F R, ∃ r : NNReal, r ≠ 0 ∧ HasLen v R (OmType AA.carrier χ) r) ∧ ∀ r : ℕ → NNReal, (∀ m ∈ Finset.Icc 1 (p ^ f - 1), HasLen v R (OmType AA.carrier (σ ^ m)) (r m)) → HasLen v R (OmAA AA.carrier) (∏ m ∈ Finset.Icc 1 (p ^ f - 1), r m) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_ideal | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_ideal | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_ideal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupCharactersStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_characters : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (χ : MulChar F R) (a b c : NNReal), HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) χ) a → HasLen v R (OmType (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) χ) b → HasLen v R (OmType AA.carrier χ) c → a * b ≤ c := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_characters | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_characters | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_characters <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TensorProductHopfOrdersStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_product_hopf_orders : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), ∃ AA : HopfOrder (C := C) R (N₁ × N₂), AA.carrier = tens A₁.carrier A₂.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) = A₁.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) = A₂.carrier ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (z.1, 0)) ∈ AA.carrier) ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (0, z.2)) ∈ AA.carrier) ∧ ∀ c₁ c₂, HasColen R v A₁.carrier c₁ → HasColen R v A₂.carrier c₂ → HasColen R v AA.carrier (c₁ ^ Fintype.card N₂ * c₂ ^ Fintype.card N₁) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tensor_product_hopf_orders | exact GlobalTheory.CompanionTheory.Relay.tensor_product_hopf_orders | (intros; apply GlobalTheory.CompanionTheory.Relay.tensor_product_hopf_orders <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TensorProductTightHopfOrdersStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_product_tight_hopf_orders : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), (∀ x : N₁, p • x = 0) → (∀ x : N₂, p • x = 0) → IsTight v p A₁.carrier → IsTight v p A₂.carrier → IsTight v p (tens A₁.carrier A₂.carrier) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tensor_product_tight_hopf_orders | exact GlobalTheory.CompanionTheory.Relay.tensor_product_tight_hopf_orders | (intros; apply GlobalTheory.CompanionTheory.Relay.tensor_product_tight_hopf_orders <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValuationLatticeMatrixReductionStatement
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_lattice_matrix_reduction : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (τ : S) (r : S → ℕ) (W : Type) [AddCommGroup W] [Module C W] [Module w.valuationSubring W] [IsScalarTower w.valuationSubring C W] (g : S → (Fin (p + q) → C) →ₗ[C] W) (v : Fin p → W) (U : Fin (p + q) → Fin (p + q) → C) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), Function.Injective a → (∀ f : S → Fin (p + q) → C, ∑ s, g s (f s) = 0 → ∀ s, g s (f s) = 0) → (∀ s, Module.finrank C (LinearMap.ker (g s)) = r s) → r τ = q → LinearIndependent C v → (∀ y, y ∈ Submodule.span w.valuationSubring (Set.range v) ↔ y ∈ LinearMap.range (g τ) ∧ ∃ f ∈ freeLattice a (p + q), ∑ s, g s (f s) = y) → (∀ i, g τ (U (Fin.castAdd q i)) = v i) → (∀ j, g τ (U (Fin.natAdd p j)) = 0) → IsLatticeBasis w (fun j => U (Fin.natAdd p j)) (eigenQuot (W := fun _ => Fin (p + q) → C) (kerFil a (p + q) g) τ) → IsLatticeBasis w (fun i => ∑ j, A i j • U j) (eigenQuot (W := fun _ => Fin (p + q) → C) (freeLattice a (p + q)) τ) → ∃ ε : (w.valuationSubring)ˣ, A.det * (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C))) ^ (p + q) = (ε : w.valuationSubring) * ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ^ r s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.Core.det_adapted_core | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.Core.det_adapted_core | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.Core.det_adapted_core <;> assumption)
end

