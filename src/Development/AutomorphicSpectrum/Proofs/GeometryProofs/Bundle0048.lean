module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0042
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedSpan
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.AdaptedSpan

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

section

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module Ω V]
  {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ}

theorem comp_act (𝓗 : HodgeLat L ρ bar r) {σ : E →+* Ω} {φ : Module.Dual Ω V}
    (h : ((0 : V), φ) ∈ HT.eigSp 𝓗.ρH σ) (a : 𝓞 E) : φ ∘ₗ ρ (bar a) = σ (a : E) • φ := by
  have h1 := (HT.LatBasic.mem_eigSp.mp h) a
  rw [𝓗.act_inr] at h1
  exact congrArg Prod.snd h1

theorem comp_eigProj (𝓗 : HodgeLat L ρ bar r) {σ σ' : E →+* Ω}
    (hσ : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (hb : ∀ a, bar (bar a) = a) {φ : Module.Dual Ω V}
    (h : ((0 : V), φ) ∈ HT.eigSp 𝓗.ρH σ) : φ ∘ₗ HT.eigProj ρ σ' = φ := by
  have key : ∀ b : 𝓞 E, φ ∘ₗ ρ b = σ' (b : E) • φ := by
    intro b
    have h1 := comp_act 𝓗 h (bar b)
    rw [hb b] at h1
    rw [h1, hσ b]
  have hsum : ∑ k, σ' (HT.dualInt E k) * σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    have h1 := congrArg σ' (HT.LatBasic.sum_dualInt_mul (E := E))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, NumberField.integralBasis_apply]
  unfold HT.eigProj
  ext x
  have hk : ∀ k, φ ((σ' (HT.dualInt E k) • ρ (RingOfIntegers.basis E k)) x) =
      σ' (HT.dualInt E k) * σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) * φ x := by
    intro k
    have e := LinearMap.congr_fun (key (RingOfIntegers.basis E k)) x
    rw [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at e
    rw [LinearMap.smul_apply, map_smul, e, smul_eq_mul, mul_assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  simp_rw [hk]
  rw [← Finset.sum_mul, hsum, one_mul]

end

theorem adapted_span : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω]
    (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V]
    (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (p q r : ℕ) (𝓗 : HodgeLat L ρ bar r)
    (σ σ' : E →+* Ω) (v : Fin p → V) (w : Fin q → V) (u : Fin (p + q) → V × Module.Dual Ω V),
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent Ω v →
    Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω w →
    Submodule.span Ω (Set.range w) = HT.eigSp ρ σ' → IsAdapted 𝓗.ρH σ v w u →
    LinearIndependent Ω u ∧ Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ ∧
      ∀ φ : Module.Dual Ω V, ((0 : V), φ) ∈ HT.eigSp 𝓗.ρH σ → φ ∘ₗ HT.eigProj ρ σ' = φ := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar p q r 𝓗 σ σ' v w u hσ hb hv hvs hw hws hu
  obtain ⟨hu1, hu2, hu3⟩ := hu
  have hz : ∀ j, (u (Fin.natAdd p j)).1 = 0 := fun j => (hu3 j).1
  have hz2 : ∀ j j', (u (Fin.natAdd p j)).2 (w j') = if j = j' then 1 else 0 := fun j => (hu3 j).2
  have hli : LinearIndependent Ω u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    have h1 : ∀ i, g (Fin.castAdd q i) = 0 := by
      have hf := congrArg Prod.fst hg
      simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hu2, hz] at hf
      exact Fintype.linearIndependent_iff.mp hv _ hf
    have h2 : ∀ j, g (Fin.natAdd p j) = 0 := by
      intro j'
      have hs := congrArg (fun y : V × Module.Dual Ω V => y.2 (w j')) hg
      simpa [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, h1, hz2] using hs
    intro i
    exact Fin.addCases h1 h2 i
  have hspan : Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hu1 i
    · intro y hy
      have hy1 : y.1 ∈ HT.eigSp ρ σ := by
        rw [HT.LatBasic.mem_eigSp]
        intro a
        have h1 := congrArg Prod.fst ((HT.LatBasic.mem_eigSp.mp hy) a)
        rw [𝓗.act_fst] at h1
        exact h1
      rw [← hvs, Submodule.mem_span_range_iff_exists_fun] at hy1
      obtain ⟨c, hc⟩ := hy1
      set y' := y - ∑ i, c i • u (Fin.castAdd q i) with hy'
      have hy'mem : y' ∈ HT.eigSp 𝓗.ρH σ :=
        Submodule.sub_mem _ hy (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hu1 _))
      have hy'1 : y'.1 = 0 := by
        simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hy', hu2, hc]
      set χ := y'.2 - ∑ j, y'.2 (w j) • (u (Fin.natAdd p j)).2 with hχ
      have hχmem : ((0 : V), χ) ∈ HT.eigSp 𝓗.ρH σ := by
        have e : ((0 : V), χ) = y' - ∑ j, y'.2 (w j) • u (Fin.natAdd p j) := by
          refine Prod.ext ?_ ?_
          · simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hy'1, hz]
          · simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hχ]
        rw [e]
        exact Submodule.sub_mem _ hy'mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hu1 _))
      have hχw : ∀ j', χ (w j') = 0 := by
        intro j'
        simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hχ, hz2]
      have hχker : HT.eigSp ρ σ' ≤ LinearMap.ker χ := by
        rw [← hws, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact hχw j
      have hχ0 : χ = 0 := by
        have h2 := comp_eigProj 𝓗 hσ hb hχmem
        ext x
        rw [← h2, LinearMap.comp_apply, LinearMap.zero_apply]
        exact LinearMap.mem_ker.mp (hχker (HT.LatBasic.eigProj_mem ρ σ' x))
      have hy2 : y'.2 = ∑ j, y'.2 (w j) • (u (Fin.natAdd p j)).2 := sub_eq_zero.mp hχ0
      have hT : y' = ∑ j, y'.2 (w j) • u (Fin.natAdd p j) := by
        refine Prod.ext ?_ ?_
        · simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hy'1, hz]
        · simpa [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] using hy2
      have hyeq : y = ∑ i, c i • u (Fin.castAdd q i) + ∑ j, y'.2 (w j) • u (Fin.natAdd p j) := by
        rw [← hT, hy']
        abel
      rw [hyeq]
      exact Submodule.add_mem _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  exact ⟨hli, hspan, fun φ hφ => comp_eigProj 𝓗 hσ hb hφ⟩

end GlobalTheory.CompanionTheory.Ar.Flat.AdaptedSpan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLine
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem hermLine_pull_blockMap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k), IsBlockMap κ v → (∀ A : HermLine ι, ∃! A' : HermLine ι', IsPullHerm κ v A A') ∧ (∀ (A : HermLine ι) (A' : HermLine ι'), IsPullHerm κ v A A' → IsSmoothHerm A → IsSmoothHerm A') ∧ (∀ (P' : Ideal (MRing ι')), ∀ z ∈ mcPts P', (fun p => z (v p)) ∈ mcPts (imageZ v P')) ∧ ∀ (z : (Σ k, ι' k) → ℂ) (f : MRing ι), evC z (rename v f) = evC (fun p => z (v p)) f :=
  @PositivityTheory.UnitarySelfGeneration.j_pull

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqOfHopfEmbedding
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem btOrder_eq_of_open_cover : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)), Γ.IsEmb A j → IsOpenImmersion j → Γ.TranslatesCover A j ⊤ → Γ.btOrder ⊤ = A :=
  @PositivityTheory.HtPt.Mh.char

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartRingIntegralClosureFiniteStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ring_integral_closure_finite : ∀ {o : Type} [CommRing o] [Algebra.EssFiniteType ℤ o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → Module.Finite (chRing o (fun k => algebraMap Ω Ω' (x k)) c) (integralClosure (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartFinite.finite_integralClosure_chRing | exact GlobalTheory.CompanionTheory.Ar.ChartFinite.finite_integralClosure_chRing | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartFinite.finite_integralClosure_chRing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigProjMemOfFree
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.QuotEig

section Free

variable {K : Type} [Field K] {A : Subring K} {W : Type} [AddCommGroup W] [Module K W]
  {E : Type} [Field E] [NumberField E] {ρ : 𝓞 E →+* Module.End K W} {Y : Submodule A W} {N : ℕ} {t : Fin N → W}

theorem act_mem_of_free (h : HT.IsFreeOn ρ Y t) (a : 𝓞 E) {y : W} (hy : y ∈ Y) : ρ a y ∈ Y := by
  have key : Y ≤ Y.comap ((ρ a).restrictScalars A) := by
    conv_lhs => rw [h.2.2]
    rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    change ρ a (ρ (RingOfIntegers.basis E q.2) (t q.1)) ∈ Y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Module.End.mul_apply, ← map_mul, h.2.2,
      ← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E q.2), map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(q.1, k), rfl⟩)) _
  exact key hy

theorem eigProj_mem_of_free (h : HT.IsFreeOn ρ Y t) (σ : E →+* K) (hσ : ∀ a : E, σ a ∈ A) {y : W} (hy : y ∈ Y) :
    HT.eigProj ρ σ y ∈ Y := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  exact Y.smul_mem (⟨_, hσ (HT.dualInt E k)⟩ : A) (act_mem_of_free h _ hy)

end Free

section Main

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module Ω V]
  {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ}

theorem fst_eigProj (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (y : V × Module.Dual Ω V) :
    (HT.eigProj 𝓗.ρH σ y).1 = HT.eigProj ρ σ y.1 := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, 𝓗.act_fst]

theorem mem_L_iff (𝓗 : HodgeLat L ρ bar r) (x : Cpt ξ) {z : V} :
    z ∈ L x ↔ ∃ h ∈ 𝓗.HL x, h.1 = z := by
  have e : L x = (𝓗.HL.map (LinearMap.fst Ω V (Module.Dual Ω V))) x := congrFun 𝓗.map_fst.symm x
  rw [e]
  exact Iff.rfl

end Main

theorem quot_eig : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (x : Cpt ξ), (∀ a : E, σ a ∈ regAt ξ x) → (∀ y, y ∈ 𝓗.quot σ x ↔ y ∈ 𝓗.HL x ∧ y ∈ HT.eigSp 𝓗.ρH σ) ∧ (∀ z ∈ L x, HT.eigProj ρ σ z ∈ L x) ∧ (𝓗.quot σ x).map ((LinearMap.fst Ω V (Module.Dual Ω V)).restrictScalars (regAt ξ x)) = (L.inter (HT.eigSp ρ σ)) x := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar r 𝓗 σ x hσ
  obtain ⟨U, hU, t, ht⟩ := 𝓗.free x
  have hfree := ht x hU
  have hstab : ∀ {h}, h ∈ 𝓗.HL x → HT.eigProj 𝓗.ρH σ h ∈ 𝓗.HL x := fun hh =>
    eigProj_mem_of_free hfree σ hσ hh
  refine ⟨fun y => ⟨?_, ?_⟩, fun z hz => ?_, ?_⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨hstab hh, HT.LatBasic.eigProj_mem _ _ _⟩
  · rintro ⟨h1, h2⟩
    exact ⟨y, h1, HT.LatBasic.eigProj_of_mem h2⟩
  · obtain ⟨h, hh, rfl⟩ := (mem_L_iff 𝓗 x).1 hz
    exact (mem_L_iff 𝓗 x).2 ⟨_, hstab hh, fst_eigProj 𝓗 σ h⟩
  · ext z
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      have e : (HT.eigProj 𝓗.ρH σ h).1 = HT.eigProj ρ σ h.1 := fst_eigProj 𝓗 σ h
      refine ⟨(mem_L_iff 𝓗 x).2 ⟨_, hstab hh, rfl⟩, ?_⟩
      change (HT.eigProj 𝓗.ρH σ h).1 ∈ HT.eigSp ρ σ
      rw [e]
      exact HT.LatBasic.eigProj_mem _ _ _
    · rintro ⟨hz, hz'⟩
      obtain ⟨h, hh, rfl⟩ := (mem_L_iff 𝓗 x).1 hz
      refine ⟨HT.eigProj 𝓗.ρH σ h, ⟨h, hh, rfl⟩, ?_⟩
      exact (fst_eigProj 𝓗 σ h).trans (HT.LatBasic.eigProj_of_mem hz')

end GlobalTheory.CompanionTheory.Ar.Flat.QuotEig
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EmbeddingBaseChangeCompat
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

open PositivityTheory.HtPt.Mh in
theorem isEmb_baseChange_square : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ (A : Subalgebra R (T → R)) (A' : Subalgebra R' (T → R')) (ψ : A →+* A'), (∀ (a : A) t, (ψ a).1 t = algebraMap R R' (a.1 t)) → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)) (j' : Γ'.G.left ⟶ Spec (CommRingCat.of A')), Γ.IsEmb A j → Γ'.IsEmb A' j' → F ≫ j = j' ≫ Spec.map (CommRingCat.ofHom ψ) := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF A A' ψ hψ j j' hj hj'
  obtain ⟨B, _, i, k, k', σ, hk, hki, hki', -, hσ, hσ'⟩ := hF.pts
  have hhom_ext {f g : Γ'.G.left ⟶ Spec (CommRingCat.of A)}
      (h : ∀ t, (Γ'.pt t).left ≫ f = (Γ'.pt t).left ≫ g) : f = g := by
    apply pb_ext
    intro a
    rw [← sub_eq_zero]
    refine PositivityTheory.HtPt.Twhopf.sec_inj R' T Γ' ⊤ _ fun t _ => ?_
    change val (Γ'.pt t).left (pb f a - pb g a) = 0
    rw [map_sub, val_pb_comp, h, ← val_pb_comp, sub_self]
  refine hhom_ext fun t => ?_
  have h1 : σ t ≫ j = Spec.map (CommRingCat.ofHom
      (i.comp ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom))) := by
    obtain ⟨c, hc⟩ := Spec.map_surjective (σ t ≫ j)
    have h2 := hj.pt t
    rw [← hσ t, Category.assoc, ← hc, ← CommRingCat.ofHom_hom c, spec_comp, ← hki] at h2
    rw [← hc, ← CommRingCat.ofHom_hom c]
    congr 2
    exact RingHom.ext fun a => hk (RingHom.congr_fun (spec_inj h2) a)
  rw [← Category.assoc, ← hσ', Category.assoc, h1, spec_comp, ← Category.assoc, hj'.pt t, spec_comp,
    ← RingHom.comp_assoc, hki']
  congr 2
  exact RingHom.ext fun a => congrArg (algebraMap R' (FractionRing R')) (hψ a t).symm

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFrameInter
section
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.InterFrame

theorem exists_frame_inter : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (p r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (v : Fin p → V) (x : Cpt ξ), (∀ z ∈ L x, HT.eigProj ρ σ z ∈ L x) → LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → (∃ (n : ℕ) (b : Fin n → V), L.IsFrameAt b x) → ∃ P : Matrix (Fin p) (Fin p) Ω, (L.inter (HT.eigSp ρ σ)).IsFrameAt (fun i => ∑ j, P i j • v j) x := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar p r 𝓗 σ v x hst hv hsp _
  have hrange : LinearMap.range (HT.eigProj ρ σ) = HT.eigSp ρ σ := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      exact HT.LatBasic.eigProj_mem ρ σ w
    · intro w hw
      exact ⟨w, HT.LatBasic.eigProj_of_mem hw⟩
  have hidem : HT.eigProj ρ σ ∘ₗ HT.eigProj ρ σ = HT.eigProj ρ σ :=
    LinearMap.ext fun w => HT.LatBasic.eigProj_of_mem (HT.LatBasic.eigProj_mem ρ σ w)
  have hVB : L.IsVBOn {x} (Module.finrank Ω V) ⊤ := fun q _ => by
    obtain ⟨U, hU, b, hb, h⟩ := 𝓗.vb q trivial
    exact ⟨U, hU, b, hb, fun q' _ hq' => h q' trivial hq'⟩
  have h := EigSplit.isVBOn_inter_range L {x} _ (HT.eigProj ρ σ) hidem hVB
    (fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact hst)
  rw [hrange] at h
  obtain ⟨U, hU, f, hf, hfr⟩ := h x rfl
  have hfx := hfr x rfl hU
  have hn : Module.finrank Ω (HT.eigSp ρ σ) = p := by
    rw [← hsp, finrank_span_eq_card hv, Fintype.card_fin]
  subst hn
  have hmem : ∀ i, f i ∈ Submodule.span Ω (Set.range v) := fun i => by
    rw [hsp, ← hf]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose P hP using fun i => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hmem i)
  refine ⟨Matrix.of P, ?_⟩
  simpa only [Matrix.of_apply, hP] using hfx

end GlobalTheory.CompanionTheory.Ar.Flat.InterFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsJoinModelDominates
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem join_exists : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (κ' : Type) [Finite κ'] (w : κ' → Ω'), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → (∃ l, w l ≠ 0) → Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ → ∃ (M' : PModel o (joinCo i x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f i := by
  intro o _ Ω _ _ κ _ x M Ω' _ _ i κ' _ w hi ⟨l, hl⟩ hcl
  let p : Cpt M.ξ := ⟨genPt M.ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := M.tie.cover p
  have hic : i (x c) ≠ 0 := (map_ne_zero i).2 hc.1
  have hJ : joinCo i x w (c, l) ≠ 0 := mul_ne_zero hic hl
  have hgen : ∀ j l', joinCo i x w (j, l') / joinCo i x w (c, l) ∈ chRing o (joinCo i x w) (c, l) :=
    fun j l' => Algebra.subset_adjoin ⟨(j, l'), rfl⟩
  have hmap : ∀ a ∈ chRing o x c, i a ∈ chRing o (joinCo i x w) (c, l) := by
    intro a ha
    have ha' : a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := ha
    induction ha' using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      have : i (x j / x c) = joinCo i x w (j, l) / joinCo i x w (c, l) := by
        simp only [joinCo, map_div₀]
        rw [mul_div_mul_right _ _ hl]
      rw [this]
      exact hgen _ _
    | algebraMap r =>
      rw [hi]
      exact Subalgebra.algebraMap_mem _ r
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact add_mem (hy (by assumption)) (hz (by assumption))
    | mul y z _ _ hy hz =>
      rw [map_mul]
      exact mul_mem (hy (by assumption)) (hz (by assumption))
  have hAF : ∀ a ∈ chRing o (joinCo i x w) (c, l),
      a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') :=
    fun a ha => Subfield.subset_closure ha
  have hiF : ∀ a : Ω, i a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
    intro a
    have h2 := (_root_.GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation o Ω κ x M c p hc).2
    have key : ∀ b ∈ regAt M.ξ p, i b ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
      intro b hb
      obtain ⟨s, hs, t, ht, -, rfl⟩ := (h2 b).1 hb
      rw [map_div₀]
      exact div_mem (hAF _ (hmap _ hs)) (hAF _ (hmap _ ht))
    obtain ⟨u, hu, v, hv, -, rfl⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.regAt_local_mono_frac M.X Ω M.ξ).2.2 M.tie.gen p a
    rw [map_div₀]
    exact div_mem (key u hu) (key v hv)
  have hw : ∀ l', w l' / w l ∈ chRing o (joinCo i x w) (c, l) := by
    intro l'
    have : w l' / w l = joinCo i x w (c, l') / joinCo i x w (c, l) := by
      simp only [joinCo]
      rw [mul_div_mul_left _ _ hic]
    rw [this]
    exact hgen _ _
  have hle : Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) ≤
      Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      exact hiF a
    · rintro _ ⟨a, b, rfl⟩
      rw [← div_div_div_cancel_right₀ hl (w a) (w b)]
      exact div_mem (hAF _ (hw a)) (hAF _ (hw b))
  have hfrac : ∀ a : Ω', ∃ u ∈ chRing o (joinCo i x w) (c, l), ∃ v ∈ chRing o (joinCo i x w) (c, l),
      a = u / v := by
    intro a
    have ha : a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') :=
      hle (by rw [hcl]; exact Subfield.mem_top a)
    obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 ha
    have hs : Subring.closure (chRing o (joinCo i x w) (c, l) : Set Ω') =
        (chRing o (joinCo i x w) (c, l)).toSubring :=
      Subring.closure_eq (chRing o (joinCo i x w) (c, l)).toSubring
    rw [hs] at hy hz
    exact ⟨y, hy, z, hz, rfl⟩
  obtain ⟨M'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.nonempty_pModel_of_chart o Ω' (κ × κ') (joinCo i x w) ⟨(c, l), hJ, hfrac⟩
  have hctr : ∀ p', p' ∈ ctrSet o x i M'.ξ := fun p' => (_root_.GlobalTheory.CompanionTheory.Ar.join_points_charts o Ω κ κ' x Ω' i w M' hi p').1
  obtain ⟨f, hf, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates o Ω κ x M o Ω' (κ × κ') (joinCo i x w) M' i hctr
  exact ⟨M', f, hf⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPermNormalizedMinorsStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_normalized_minors : ∀ {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F), (∀ (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin r) (I : Fin k → Fin r), NormAt O Y (k + 1) hk I' → NormAt O Y k (Nat.le_of_succ_le hk) I → ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧ NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f)) → (∀ (k : ℕ) (hk : k ≤ r), ∃ I : Fin k → Fin r, NormAt O Y k hk I) → ∃ w : Equiv.Perm (Fin r), ∀ (k : ℕ) (hk : k ≤ r), NormAt O Y k hk (w ∘ Fin.castLE hk) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_perm_normAt | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_perm_normAt | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_perm_normAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreCurveDegreeCompare
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fibreCurve_curveIn_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → ∃ Y : Crv.CurveIn Γ.C Γ.η, Y.x = Γ.z ∧ ∀ (L : Lat ξ Ω) (n : ℤ), L.IsVB 1 ⊤ → (Γ.HasDeg L n ↔ Y.IsDeg L n) :=
  @PositivityTheory.Xgn.exists_curve_in_fibre_degree

end GlobalTheory.CompanionTheory.Ar.Flat
end

