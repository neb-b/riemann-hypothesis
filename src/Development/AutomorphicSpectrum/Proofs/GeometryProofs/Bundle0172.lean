module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperGroupGermFiniteSubscheme
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionSum
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0116
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperGroupGermFiniteSubschemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_group_germ_finite_subscheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left →
    ∃ (A' : Type) (_ : CommRing A') (_ : HopfAlgebra k A') (_ : Coalgebra.IsCocomm k A') (_ : Module.Finite k A'),
      Module.finrank k A' = Module.finrank k A ∧
      ∃ (D : LinearMap.ker (Matrix.toLin' (rho g.B a)) →ₗ[k] (A' →ₗ[k] k))
        (T : LinearMap.ker (Matrix.toLin' (rho g.B (star a))) →ₗ[k] A'),
        Function.Injective D ∧ Function.Injective T ∧
        (∀ u f f', D u (f * f') = D u f * Coalgebra.counit (R := k) f' + Coalgebra.counit (R := k) f * D u f') ∧
        (∀ z, Coalgebra.comul (R := k) (T z) = T z ⊗ₜ[k] (1 : A') + (1 : A') ⊗ₜ[k] T z) ∧
        ∀ (u : LinearMap.ker (Matrix.toLin' (rho g.B a))) (z : LinearMap.ker (Matrix.toLin' (rho g.B (star a)))),
          (z : Fin d → k) ⬝ᵥ (bil (g.B.ad a) 1 1).transpose.mulVec (u : Fin d → k) = 0 → D u (T z) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.KerGeom.kerHopf_geom | exact GlobalTheory.CompanionTheory.Ar.Flat.KerGeom.kerHopf_geom | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.KerGeom.kerHopf_geom <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperOfProperCover
section
open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isProper_of_finite_cover (X S : Scheme.{0}) (p : X ⟶ S) (n : ℕ) (Y : Fin n → Scheme.{0})
    (π : ∀ i, Y i ⟶ X) (hsep : IsSeparated p) (hft : LocallyOfFiniteType p)
    (hprop : ∀ i, IsProper (π i ≫ p)) (hcov : ∀ x : X, ∃ i, x ∈ Set.range (π i)) :
    IsProper p := by
  have huc : UniversallyClosed p := by
    constructor
    intro X' Y' i₁ i₂ f' hpb Z hZ
    have hW : ∀ i, IsPullback (pullback.fst i₁ (π i) ≫ f') (pullback.snd i₁ (π i)) i₂
        (π i ≫ p) := fun i => (IsPullback.of_hasPullback i₁ (π i)).paste_horiz hpb
    have hc : ∀ i, IsClosedMap ⇑(pullback.fst i₁ (π i) ≫ f') := fun i =>
      @UniversallyClosed.universally_isClosedMap _ _ _ (hprop i).toUniversallyClosed
        _ _ _ _ _ (hW i)
    have key : ⇑f' '' Z =
        ⋃ i, ⇑(pullback.fst i₁ (π i) ≫ f') '' (⇑(pullback.fst i₁ (π i)) ⁻¹' Z) := by
      ext y
      simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, y', hy'⟩ := hcov (i₁ x)
        obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x y' hy'.symm
        refine ⟨i, w, ?_, ?_⟩
        · rw [hw]
          exact hx
        · show f' (pullback.fst i₁ (π i) w) = f' x
          rw [hw]
      · rintro ⟨i, w, hw, rfl⟩
        exact ⟨pullback.fst i₁ (π i) w, hw, rfl⟩
    convert isClosed_iUnion_of_finite fun i =>
      hc i _ (hZ.preimage (pullback.fst i₁ (π i)).continuous) using 1
  exact @IsProper.mk _ _ _ hsep huc hft

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumLatticeWedgeComap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.BlockFrame

theorem frame_of_sum_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (P Wv : Type) [AddCommGroup P] [Module Ω P] [AddCommGroup Wv] [Module Ω Wv] (i : Wv →ₗ[Ω] P) (A B : Lat ξ P) (Va Vb : Submodule Ω P) (N j : ℕ) (hj : j ≤ N) (b : Fin N → Wv) (s : Fin (N - j) → P) (p : Cpt ξ), Function.Injective i → LinearMap.range i = Va ⊔ Vb → Disjoint Va Vb → (∀ x ∈ A p, x ∈ Va) → (∀ x ∈ B p, x ∈ Vb) → (Lat.comap (fun q => A q ⊔ B q) i).IsFrameAt b p → Submodule.span Ω (Set.range (b ∘ headIdx hj)) = Va.comap i → (∀ k, s k ∈ Vb ∧ i (b (tailIdx hj k)) - s k ∈ Va) → B.IsFrameAt s p ∧ (∀ k, i (b (tailIdx hj k)) - s k ∈ A p) ∧ ∀ k, i (b (headIdx hj k)) ∈ A p := by
  intro X Ω _ ξ P Wv _ _ _ _ i A B Va Vb N j hj b s p hinj hrange hdisj hAV hBV hfr hhead hs
  have hzero : ∀ {x : P}, x ∈ Va → x ∈ Vb → x = 0 := fun h1 h2 => Submodule.disjoint_def.1 hdisj _ h1 h2
  have hmemfr : ∀ k, i (b k) ∈ A p ⊔ B p := fun k => by
    have h : b k ∈ (Lat.comap (fun q => A q ⊔ B q) i) p := by
      rw [hfr.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact h
  have hbhead : ∀ k, i (b (headIdx hj k)) ∈ Va := fun k => by
    have h : b (headIdx hj k) ∈ Va.comap i := by
      rw [← hhead]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact h
  have hH : ∀ k, i (b (headIdx hj k)) ∈ A p := fun k => by
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 (hmemfr (headIdx hj k))
    have he0 : e = 0 := hzero (by
      have h : e = i (b (headIdx hj k)) - a := by rw [← hae]; abel
      rw [h]
      exact Va.sub_mem (hbhead k) (hAV a ha)) (hBV e he)
    rw [← hae, he0, add_zero]
    exact ha
  have hT : ∀ k, i (b (tailIdx hj k)) - s k ∈ A p ∧ s k ∈ B p := fun k => by
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 (hmemfr (tailIdx hj k))
    have hes : e - s k = 0 := hzero (by
      have h : e - s k = (i (b (tailIdx hj k)) - s k) - a := by rw [← hae]; abel
      rw [h]
      exact Va.sub_mem (hs k).2 (hAV a ha)) (Vb.sub_mem (hBV e he) (hs k).1)
    have hes' : e = s k := sub_eq_zero.1 hes
    refine ⟨?_, hes' ▸ he⟩
    have h : i (b (tailIdx hj k)) - s k = a := by rw [← hae, hes']; abel
    rw [h]
    exact ha
  have hcase : ∀ k : Fin N, (∃ a, k = headIdx hj a) ∨ ∃ a, k = tailIdx hj a := fun k => by
    by_cases h : (k : ℕ) < j
    · exact Or.inl ⟨⟨k, h⟩, by ext; rfl⟩
    · exact Or.inr ⟨⟨k - j, by have := k.2; omega⟩, by ext; simp [tailIdx]; omega⟩
  have hspan : ∀ x ∈ Submodule.span (regAt ξ p) (Set.range b),
      ∃ t ∈ Submodule.span (regAt ξ p) (Set.range s), i x - t ∈ Va := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rcases hcase k with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact ⟨0, zero_mem _, by simpa using hbhead a⟩
      · exact ⟨s a, Submodule.subset_span ⟨a, rfl⟩, (hs a).2⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨t, ht, hxt⟩ := hx
      obtain ⟨t', ht', hyt⟩ := hy
      refine ⟨t + t', add_mem ht ht', ?_⟩
      have h : i (x + y) - (t + t') = (i x - t) + (i y - t') := by rw [map_add (f := _)]; abel
      rw [h]
      exact Va.add_mem hxt hyt
    | smul r x _ hx =>
      obtain ⟨t, ht, hxt⟩ := hx
      refine ⟨r • t, Submodule.smul_mem _ r ht, ?_⟩
      have h : i (r • x) - r • t = (r : Ω) • (i x - t) := by
        rw [smul_sub]
        show i ((r : Ω) • x) - (r : Ω) • t = _
        rw [map_smul]
      rw [h]
      exact Va.smul_mem _ hxt
  have hle : Submodule.span (regAt ξ p) (Set.range s) ≤ B p := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact (hT k).2)
  have hgen : B p = Submodule.span (regAt ξ p) (Set.range s) := by
    refine le_antisymm (fun e he => ?_) hle
    have hr : e ∈ LinearMap.range i := by
      rw [hrange]
      exact Submodule.mem_sup_right (hBV e he)
    obtain ⟨x, rfl⟩ := hr
    have hxc : x ∈ (Lat.comap (fun q => A q ⊔ B q) i) p := by
      show i x ∈ A p ⊔ B p
      exact Submodule.mem_sup_right he
    rw [hfr.2] at hxc
    obtain ⟨t, ht, hxt⟩ := hspan x hxc
    have h0 : i x - t = 0 := hzero hxt (Vb.sub_mem (hBV _ he) (hBV _ (hle ht)))
    rw [sub_eq_zero.1 h0]
    exact ht
  have htinj : Function.Injective (tailIdx hj) := fun a c h => by
    have h' := congrArg Fin.val h
    simp only [tailIdx] at h'
    ext
    omega
  have hli : LinearIndependent Ω s := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    have hx1 : (∑ k, g k • b (tailIdx hj k)) ∈ Va.comap i := by
      have h : i (∑ k, g k • b (tailIdx hj k)) = ∑ k, g k • (i (b (tailIdx hj k)) - s k) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib, hg, sub_zero]
      show i _ ∈ Va
      rw [h]
      exact Va.sum_mem fun k _ => Va.smul_mem _ (hs k).2
    have hdis : Disjoint (Set.range (headIdx hj)) (Set.range (tailIdx hj)) := by
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨a, rfl⟩ ⟨c, h⟩
      have h' := congrArg Fin.val h
      simp only [headIdx, tailIdx, Fin.val_castLE] at h'
      have := a.2
      omega
    have hd := hfr.1.disjoint_span_image hdis
    have hx2 : (∑ k, g k • b (tailIdx hj k)) ∈ Submodule.span Ω (b '' Set.range (tailIdx hj)) :=
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨_, ⟨k, rfl⟩, rfl⟩)
    have hx3 : (∑ k, g k • b (tailIdx hj k)) ∈ Submodule.span Ω (b '' Set.range (headIdx hj)) := by
      rw [← Set.range_comp, hhead]
      exact hx1
    have hx0 := Submodule.disjoint_def.1 hd _ hx3 hx2
    exact Fintype.linearIndependent_iff.1 (hfr.1.comp _ htinj) g hx0
  exact ⟨⟨hli, hgen⟩, fun k => (hT k).1, hH⟩

end GlobalTheory.CompanionTheory.Ar.BlockFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorWedgeDetChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.TopWedge

theorem exists_form_tprod_wedge (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] (V : Ψ → Type)
    [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)] (n : ℕ) (e : ∀ τ, Fin n → V τ)
    (hli : ∀ τ, LinearIndependent Ω (e τ)) (hspan : ∀ τ, Submodule.span Ω (Set.range (e τ)) = ⊤) :
    ∃ Φ : (PiTensorProduct Ω fun τ => ⋀[Ω]^n (V τ)) →ₗ[Ω] Ω,
      Φ (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e τ)) = 1 := by
  classical
  let b : ∀ τ, Module.Basis (Fin n) Ω (V τ) := fun τ => Module.Basis.mk (hli τ) (hspan τ).ge
  let φ : ∀ τ, ⋀[Ω]^n (V τ) →ₗ[Ω] Ω := fun τ => exteriorPower.alternatingMapLinearEquiv (b τ).det
  have hφ : ∀ τ, φ τ (exteriorPower.ιMulti Ω n (e τ)) = 1 := fun τ => by
    have hb : (⇑(b τ) : Fin n → V τ) = e τ := Module.Basis.coe_mk _ _
    simp only [φ, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rw [← hb]
    exact (b τ).det_self
  refine ⟨PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra Ω Ψ Ω).compLinearMap φ), ?_⟩
  rw [PiTensorProduct.lift.tprod]
  simp [hφ]

theorem eq_mul_prod_det : ∀ (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] (V : Ψ → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)] (n : ℕ) (e e' : ∀ τ, Fin n → V τ) (T : ∀ τ, Matrix (Fin n) (Fin n) Ω) (a a' : Ω), (∀ τ, LinearIndependent Ω (e τ)) → (∀ τ, Submodule.span Ω (Set.range (e τ)) = ⊤) → (∀ τ q, e' τ q = ∑ p, T τ p q • e τ p) → a • (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e τ) : PiTensorProduct Ω fun τ => ⋀[Ω]^n (V τ)) = a' • (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e' τ) : PiTensorProduct Ω fun τ => ⋀[Ω]^n (V τ)) → a = a' * ∏ τ, (T τ).det := by
  intro Ψ _ Ω _ V _ _ n e e' T a a' hli hspan hT h
  classical
  obtain ⟨Φ, hΦ⟩ := exists_form_tprod_wedge Ψ Ω V n e hli hspan
  have hq : ∀ τ, exteriorPower.ιMulti Ω n (e' τ) = (T τ).det • exteriorPower.ιMulti Ω n (e τ) := fun τ => by
    rw [← GlobalTheory.CompanionTheory.Ar.BigBlock.iotaMulti_comb]
    congr 1
    funext q
    exact hT τ q
  have htp : (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e' τ)) =
      (∏ τ, (T τ).det) • (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e τ)) := by
    simp_rw [hq]
    exact MultilinearMap.map_smul_univ _ _ _
  have h2 := congrArg Φ h
  rw [htp, map_smul, map_smul, map_smul, hΦ] at h2
  simpa using h2

end GlobalTheory.CompanionTheory.Ar.TopWedge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitValueFrameDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.UnitValue

theorem mem_regAt_of_pow_mul {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}
    {f u : Ω} (hf : f ≠ 0) (hf' : f⁻¹ ∈ regAt ξ p) {n : ℕ} (h : f ^ n * u ∈ regAt ξ p) : u ∈ regAt ξ p := by
  have hu : u = f⁻¹ ^ n * (f ^ n * u) := by
    rw [← _root_.mul_assoc, ← _root_.mul_pow, inv_mul_cancel₀ hf, _root_.one_pow, _root_.one_mul]
  rw [hu]
  exact mul_mem (pow_mem hf' n) h

private theorem valAt_unique_lemma {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hg : GlobalTheory.CompanionTheory.Ar.IsCptGen ξ) {z : Spec (CommRingCat.of ℂ) ⟶ X} {a : Ω} {r r' : ℂ}
    (h1 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z a r) (h2 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z a r') : r = r' := by
  obtain ⟨h, s, hs, rfl⟩ := h1
  obtain ⟨h', s', hs', rfl⟩ := h2
  have hss : s = s' := hg.inj ⟨GlobalTheory.CompanionTheory.Ar.centre z, h⟩ (hs.trans hs'.symm)
  rw [hss]

private theorem ne_zero_and_inv_mem_regAt_of_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre z) {a : Ω} {v : ℂ}
    (hv : v ≠ 0) (h : GlobalTheory.CompanionTheory.Ar.ValAt ξ z a v) :
    a ≠ 0 ∧ a⁻¹ ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ := by
  obtain ⟨h', s, hs, hsv⟩ := h
  have hsu : IsUnit s := by
    have hi : IsUnit ((Scheme.stalkClosedPointTo z).hom s) := by
      rw [hsv]; exact hv.isUnit
    have hloc : IsLocalHom (Scheme.stalkClosedPointTo z).hom := by infer_instance
    exact hloc.map_nonunit s hi
  refine ⟨?_, ?_⟩
  · rw [← hs]
    exact (hsu.map (GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, h'⟩)).ne_zero
  · have hva : ∃ r : ℂ, GlobalTheory.CompanionTheory.Ar.ValAt ξ z a⁻¹ r := by
      refine ⟨_, h', ↑hsu.unit⁻¹, ?_, rfl⟩
      rw [map_units_inv, IsUnit.unit_spec, hs]
    obtain ⟨r, hr⟩ := hva
    exact GlobalTheory.CompanionTheory.Ar.ChgUnit.mem_regAt_of_valAt hr _ rfl

theorem valAt_ne_zero_of_isUnitOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f u : Ω), CoordTie ℤ ξ (segreCoord y) → genPt ξ ⤳ centre z → CoordsAt ξ y z w → InFrameDomain y cc f w → IsUnitOn y cc f u → valAt y u w ≠ 0 ∧ ValAt ξ z u (valAt y u w) := by
  intro X Ω _ ξ K _ J _ y z w cc f u hT hz hC hF hU
  have hequiv := _root_.GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords X Ω ξ K J y hT z w hz hC
  have hch := GlobalTheory.CompanionTheory.Ar.ChgUnit.inChart_of_coordsAt hC cc (fun k => (hF.1 k).isUnit)
    ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ rfl
  have hreg : ∀ a, a ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) cc →
      a ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ :=
    fun a ha => (hT.ring cc hch.1 a).1 ha _ hch
  obtain ⟨v, hv, hv0⟩ := hF.2
  obtain ⟨hf0, hfi⟩ := ne_zero_and_inv_mem_regAt_of_valAt hz hv0 ((hequiv f v).2 hv)
  obtain ⟨hu0, ⟨n, hn⟩, ⟨m, hm⟩⟩ := hU
  have hu := mem_regAt_of_pow_mul hf0 hfi (hreg _ hn)
  have hui := mem_regAt_of_pow_mul hf0 hfi (hreg _ hm)
  obtain ⟨r, hr0, hr⟩ := GlobalTheory.CompanionTheory.Ar.ChgUnit.exists_value_of_unit hT.gen z hz hu0 hu hui
  have hex : ∃ v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y u w v := ⟨r, (hequiv u r).1 hr⟩
  have hval : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt y u w = hex.choose := by
    rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dite_eq_left hex]
  have hc : GlobalTheory.CompanionTheory.Ar.ValAt ξ z u hex.choose := (hequiv u _).2 hex.choose_spec
  have heq : hex.choose = r := valAt_unique_lemma hT.gen hc hr
  rw [hval, heq]
  exact ⟨hr0, hr⟩

end GlobalTheory.CompanionTheory.Ar.UnitValue
end

