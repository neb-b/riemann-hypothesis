module

public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0115
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0084
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.CptEx
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

private theorem noetherianSpace_projectiveSpectrum {A σ : Type} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℕ → σ)
    [GradedRing 𝒜] [IsNoetherianRing A] : TopologicalSpace.NoetherianSpace (ProjectiveSpectrum 𝒜) := by
  let f : ProjectiveSpectrum 𝒜 → PrimeSpectrum A := fun p => ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩
  have hf : Topology.IsInducing f := by
    refine ⟨TopologicalSpace.ext_iff_isClosed.2 fun s => ?_⟩
    rw [isClosed_induced_iff, ProjectiveSpectrum.isClosed_iff_zeroLocus]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨PrimeSpectrum.zeroLocus t, PrimeSpectrum.isClosed_zeroLocus t, ?_⟩
      ext x
      simp [f, ProjectiveSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨u, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus t).1 ht
      refine ⟨u, ?_⟩
      ext x
      simp [f, ProjectiveSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus]
  exact hf.noetherianSpace

theorem cptEx : CptEx := by
  intro E _ _ _ H D l Xo c _ Y S Ω _ K _ J _ y 𝔐
  have hfr : ∀ x : ↥c.F, ∃ (a b : 𝓞 ↥c.F), (algebraMap (𝓞 ↥c.F) ↥c.F) b ≠ 0 ∧ x * (algebraMap (𝓞 ↥c.F) ↥c.F) b = (algebraMap (𝓞 ↥c.F) ↥c.F) a := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 ↥c.F) x
    have hb' : (algebraMap (𝓞 ↥c.F) ↥c.F) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩
  have hinj : Function.Injective (algebraMap (𝓞 ↥c.F) ↥c.F) := IsFractionRing.injective _ _
  obtain ⟨hpre, hflat⟩ := GlobalTheory.CompanionTheory.Ar.Flat.spMap_flat_preimmersion (algebraMap (𝓞 ↥c.F) ↥c.F) hinj hfr
  obtain ⟨jpre, jflat⟩ := GlobalTheory.CompanionTheory.Ar.Flat.j_flat_preimmersion Y hinj hfr
  haveI := hpre
  haveI := jpre
  haveI := Y.jQ_open
  haveI : TopologicalSpace.NoetherianSpace Y.X := by
    obtain ⟨N, i, hi, -⟩ := Y.proj
    have : TopologicalSpace.NoetherianSpace (PSpace (𝓞 ↥c.F) N) := by
      unfold PSpace
      letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := 𝓞 ↥c.F)
      exact noetherianSpace_projectiveSpectrum _
    exact i.isClosedEmbedding.isInducing.noetherianSpace
  have hfx : 𝔐.f (genPt 𝔐.ξ) = genPt 𝔐.ξ₀ := GlobalTheory.CompanionTheory.Ar.Dominates.map_genPt 𝔐.fn_over
  have hsx : Y.s (genPt 𝔐.ξ₀) ∈ Set.range (spMap (algebraMap (𝓞 ↥c.F) ↥c.F)) := by
    refine ⟨spMap 𝔐.cst (IsLocalRing.closedPoint Ω), ?_⟩
    have h2 := congrArg (fun g => g (IsLocalRing.closedPoint Ω)) 𝔐.cst_over
    have h3 : spMap (𝔐.cst.comp (algebraMap (𝓞 ↥c.F) ↥c.F)) = spMap 𝔐.cst ≫ spMap (algebraMap (𝓞 ↥c.F) ↥c.F) := by
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [h3] at h2
    simp only [Scheme.Hom.comp_apply] at h2
    rw [← hfx]
    exact h2.symm
  have hsx2 : genPt 𝔐.ξ₀ ∈ Set.range (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))) := by
    rw [Scheme.Pullback.range_fst]
    exact hsx
  obtain ⟨x', hx'⟩ := hsx2
  have hgen : ∀ {p z : ↥Y.X}, genPt 𝔐.ξ₀ ⤳ p → z ⤳ p → genPt 𝔐.ξ₀ ⤳ z := fun hp hz =>
    GlobalTheory.CompanionTheory.Ar.Flat.genPt_specializes_of_specializes 𝔐.ξ₀ 𝔐.gen₀ hp hz
  have hopen : IsOpen (closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)) := by
    refine GlobalTheory.CompanionTheory.Ar.Flat.isOpen_of_isClosed_of_generizing _ isClosed_closure ?_
    intro a b hab hb
    exact specializes_iff_mem_closure.1 (hgen (specializes_iff_mem_closure.2 hb) hab)
  have hV : IsOpen ((pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base ⁻¹' closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)) :=
    hopen.preimage (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).continuous
  obtain ⟨q, hqV, u0, rfl⟩ := Y.jQ_dense.inter_open_nonempty _ hV
    ⟨x', by
      show (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base x' ∈ closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)
      rw [hx']
      exact subset_closure rfl⟩
  have hsp : x' ⤳ Y.jQ u0 := by
    rw [← (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).isEmbedding.isInducing.specializes_iff, hx']
    exact specializes_iff_mem_closure.2 hqV
  obtain ⟨u, hu⟩ := hsp.mem_open Y.jQ.isOpenEmbedding.isOpen_range ⟨u0, rfl⟩
  have hju : Y.j u = genPt 𝔐.ξ₀ := by
    show (Y.jQ ≫ pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base u = genPt 𝔐.ξ₀
    rw [Scheme.Hom.comp_apply, hu, hx']
  have hmin : ∀ z, z ⤳ u → z = u := by
    intro z hz
    have h1 : Y.j z ⤳ genPt 𝔐.ξ₀ := hju ▸ hz.map Y.j.continuous
    have h2 : genPt 𝔐.ξ₀ ⤳ Y.j z := hgen (specializes_refl _) h1
    exact Y.j.isEmbedding.injective ((h1.antisymm h2).eq.trans hju.symm)
  obtain ⟨U, hU, huU⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {u} isIrreducible_singleton
  obtain ⟨Z⟩ := GlobalTheory.CompanionTheory.Ar.Flat.nonempty_cptOver_of_fraction hinj hfr Y U hU
  have hZu : genPt Z.ξ₀ = u := hmin _ ((Z.closure u).1 (huU rfl))
  obtain ⟨U', hU', -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.cptOver_isOpen_isDomain E H D l Xo c (𝓞 ↥c.F) (algebraMap (𝓞 ↥c.F) ↥c.F) Y U Z
    ⟨hinj, inferInstance, hfr⟩
  refine ⟨U, Z, ⟨isClosed_of_mem_irreducibleComponents U hU, hU' ▸ U'.isOpen⟩, hU.1, ?_⟩
  have : genPt (Z.ξ₀ ≫ Y.j) = Y.j (genPt Z.ξ₀) := by
    unfold genPt
    exact Scheme.Hom.comp_apply _ _ _
  rw [this, hZu, hju]

end RootFieldNumerics.RF
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.FrameOfMatrix
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF.Loc

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unit_of_val {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R}
    (h : genPt ξ ⤳ centre z) (hv : ValAt ξ z a r) (hr : IsUnit r) : unitAt ξ ⟨centre z, h⟩ a := by
  obtain ⟨h', x, rfl, rfl⟩ := hv
  obtain ⟨x, rfl⟩ : IsUnit x := (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit x hr
  exact ⟨(x.isUnit.map (genMap ξ ⟨centre z, h'⟩)).ne_zero, ⟨x.val, rfl⟩, ⟨x⁻¹.val, map_units_inv _ x⟩⟩

variable {L : Type} [Field L] {z : Spec (CommRingCat.of L) ⟶ X}

theorem val_mul {a b : Ω} {r s : L} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨_, y, rfl, rfl⟩ := h'
  exact ⟨h, x * y, map_mul _ _ _, map_mul _ _ _⟩

theorem val_pow {a : Ω} {r : L} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  exact ⟨h, x ^ n, map_pow _ _ _, map_pow _ _ _⟩

theorem val_inv {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨x, rfl⟩ : IsUnit x :=
    (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit x (IsUnit.mk0 _ hr)
  exact ⟨h, x⁻¹.val, map_units_inv _ x, map_units_inv _ x⟩

theorem val_zpow {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) (n : ℤ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using val_pow h n
  · simpa using val_inv (val_pow h n) (pow_ne_zero _ hr)

end Val

theorem frame_of_matrix {S : Scheme.{0}} {L : Type} [Field L] {G : Over S} [GrpObj G] [IsCommMonObj G] {x₀ : Sp L ⟶ S}
    {W : Type} [AddCommGroup W] [Module L W] (M : LieModel G x₀ W) {O : Type} [CommRing O] (act : OAct O G)
    (ρ : O →+* Module.End L W) (σ : O →+* L) (hM : M.IsActOf act.act ρ) {n : ℕ} (x : Fin n → W)
    (hx : IsEigFrame act x₀ σ fun k => M.pt (x k)) (P : Matrix (Fin n) (Fin n) L) (hP : P.det ≠ 0) :
    LinearIndependent L (fun k => ∑ i, P k i • x i) ∧ IsEigFrame act x₀ σ (fun k => M.pt (∑ i, P k i • x i)) ∧
      ∀ k, IsComb (P k) (fun i => M.pt (x i)) (M.pt (∑ i, P k i • x i)) := by
  obtain ⟨h1, h2⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame.isEigFrame_pt_iff S L G x₀ W M O act ρ σ n x hM).1 hx
  have hU : IsUnit P.det := IsUnit.mk0 _ hP
  have key : ∀ u : Fin n → L, ∑ k, u k • ∑ i, P k i • x i = ∑ i, (Matrix.vecMul u P) i • x i := fun u => by
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have huniq : ∀ e ∈ eigSp ρ σ, ∃! cf : Fin n → L, e = ∑ k, cf k • ∑ i, P k i • x i := fun e he => by
    obtain ⟨cf, hcf, hu⟩ := h2 e he
    refine ⟨Matrix.vecMul cf P⁻¹, ?_, fun u h => ?_⟩
    · change e = ∑ k, (Matrix.vecMul cf P⁻¹) k • ∑ i, P k i • x i
      rw [key, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hU, Matrix.vecMul_one]
      exact hcf
    · have e1 : Matrix.vecMul u P = cf := hu _ (h.trans (key u))
      rw [← e1, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hU, Matrix.vecMul_one]
  refine ⟨Fintype.linearIndependent_iff.2 fun u hu k => ?_, ?_, fun k => ?_⟩
  · obtain ⟨cf, -, h0⟩ := huniq 0 (Submodule.zero_mem _)
    have e1 : u = cf := h0 u hu.symm
    have e2 : (0 : Fin n → L) = cf := h0 0 (by simp)
    rw [e1, ← e2]
    rfl
  · exact (_root_.GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame.isEigFrame_pt_iff S L G x₀ W M O act ρ σ n (fun k => ∑ i, P k i • x i) hM).2
      ⟨fun k => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h1 i), huniq⟩
  · exact (_root_.GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isComb_lieModel_pt_iff S L G x₀ W M n x (P k) _).2 rfl

theorem tied_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type}
    [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} {F : Type} [Field F]
    {z : Spec (CommRingCat.of F) ⟶ 𝔐.X} {y₀ : Sp F ⟶ Xo.XF c} {vb : epsAt z ⟶ 𝔐.t.G}
    {v v' : epsAt (under y₀) ⟶ Xo.univ.t.G} (h : Tied 𝔐 z y₀ vb v) (h' : Tied 𝔐 z y₀ vb v') : v = v' := by
  obtain ⟨u, h1, h2⟩ := h
  obtain ⟨u', h1', h2'⟩ := h'
  obtain rfl : u = u' := Over.OverMorphism.ext (h2.symm.trans h2')
  exact h1.unique_left h1'

end RootFieldNumerics.RF.Loc
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.HostRd
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

theorem chiEx : ChiEx := by
  intro E _ _ _ H _
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  have h4 : H.d % 4 = 3 := by
    have := H.d_mod
    omega
  refine ⟨(quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ), GlobalTheory.isKroneckerChar_quadraticChar h4, ?_⟩
  have hr : rootDiscr E = hostRd E := by
    simp [rootDiscr_def, hostRd, Int.cast_abs, one_div]
  have hpos : 0 < hostRd E := by
    unfold hostRd
    apply Real.rpow_pos_of_pos
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
  simp only [GlobalTheory.CM.logOm, hostLval]
  rw [Complex.sub_re, Complex.ofReal_re, hr, Real.log_div (by positivity) hpos.ne']
  ring

end RootFieldNumerics.RF
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.LogDetBounds
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF.Loc

theorem exists_basis {V L W : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field L] [Algebra V L]
    [IsFractionRing V L] [AddCommGroup W] [Module L W] [Module V W] [IsScalarTower V L W] {n : ℕ} (x : Fin n → W)
    (Λ : Submodule V W) {c : V} (hc : c ≠ 0) (h₁ : Λ ≤ Submodule.span V (Set.range x))
    (h₂ : ∀ w ∈ Submodule.span V (Set.range x), c • w ∈ Λ) :
    ∃ P Q : Matrix (Fin n) (Fin n) V, Q * P = c • (1 : Matrix (Fin n) (Fin n) V) ∧
      Submodule.span V (Set.range fun k => ∑ i, P k i • x i) = Λ := by
  classical
  let f : (Fin n → V) →ₗ[V] W := Fintype.linearCombination V x
  have hf : ∀ u, f u = ∑ i, u i • x i := fun u => Fintype.linearCombination_apply V x u
  have hfr : LinearMap.range f = Submodule.span V (Set.range x) := Fintype.range_linearCombination V x
  let N : Submodule V (Fin n → V) := Λ.comap f
  have hcN : ∀ u : Fin n → V, c • u ∈ N := fun u => by
    change f (c • u) ∈ Λ
    rw [map_smul]
    exact h₂ _ (hfr ▸ ⟨u, rfl⟩)
  let g : (Fin n → V) →ₗ[V] N := LinearMap.codRestrict N (c • LinearMap.id) hcN
  have hg : Function.Injective g := fun u u' h => by
    have : c • u = c • u' := congrArg Subtype.val h
    exact smul_right_injective _ hc this
  have hr : Module.finrank V N = n := by
    refine le_antisymm ((Submodule.finrank_le N).trans (by simp)) ?_
    simpa using LinearMap.finrank_le_finrank_of_injective hg
  let b := Module.finBasisOfFinrankEq V N hr
  refine ⟨Matrix.of fun k i => (b k : Fin n → V) i, Matrix.of fun i k => b.repr (g (Pi.single i 1)) k, ?_, ?_⟩
  · ext i i'
    have h := congrArg (fun u : N => (u : Fin n → V) i') (b.sum_repr (g (Pi.single i 1)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [h]
    simp [g, Matrix.one_apply, Pi.single_apply, eq_comm]
  · have e : (fun k => ∑ i, (Matrix.of fun k i => (b k : Fin n → V) i) k i • x i) = fun k => f (b k) :=
      funext fun k => (hf _).symm
    rw [e]
    refine le_antisymm (Submodule.span_le.2 ?_) fun w hw => ?_
    · rintro _ ⟨k, rfl⟩
      exact (b k).2
    · obtain ⟨u, rfl⟩ : w ∈ LinearMap.range f := hfr ▸ h₁ hw
      have hu : u ∈ N := hw
      have h := congrArg (fun t : N => f t) (b.sum_repr ⟨u, hu⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul] at h
      rw [← h]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem log_det_bounds {V A : Type} [CommRing V] [NormedField A] (j : V →+* A) (hj : ∀ a, ‖j a‖ ≤ 1) {n : ℕ}
    {P Q : Matrix (Fin n) (Fin n) V} {c : V} (hc : j c ≠ 0) (h : Q * P = c • (1 : Matrix (Fin n) (Fin n) V)) :
    j P.det ≠ 0 ∧ n * Real.log ‖j c‖ ≤ Real.log ‖j P.det‖ ∧ Real.log ‖j P.det‖ ≤ 0 := by
  have e : j Q.det * j P.det = j c ^ n := by
    rw [← map_mul, ← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, map_pow, Fintype.card_fin]
  have h0 : j Q.det * j P.det ≠ 0 := e ▸ pow_ne_zero _ hc
  have hP := right_ne_zero_of_mul h0
  have hQ := left_ne_zero_of_mul h0
  have e2 : Real.log ‖j Q.det‖ + Real.log ‖j P.det‖ = n * Real.log ‖j c‖ := by
    rw [← Real.log_mul (norm_ne_zero_iff.2 hQ) (norm_ne_zero_iff.2 hP), ← norm_mul, e, norm_pow, Real.log_pow]
  have a1 := Real.log_nonpos (norm_nonneg _) (hj Q.det)
  have a2 := Real.log_nonpos (norm_nonneg _) (hj P.det)
  exact ⟨hP, by linarith, a2⟩

section Ev

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]

theorem exists_ev (hξ : IsCptGen ξ) (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) :
    ∃ ev : regAt ξ ⟨centre z, h⟩ →+* R, ∀ a : regAt ξ ⟨centre z, h⟩, ValAt ξ z a (ev a) := by
  let e : X.presheaf.stalk (centre z) ≃+* regAt ξ ⟨centre z, h⟩ :=
    RingEquiv.ofBijective (genMap ξ ⟨centre z, h⟩).rangeRestrict
      ⟨fun a b hab => hξ.inj ⟨centre z, h⟩ (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  refine ⟨(Scheme.stalkClosedPointTo z).hom.comp e.symm.toRingHom, fun a => ⟨h, e.symm a, ?_, rfl⟩⟩
  exact congrArg Subtype.val (e.apply_symm_apply a)

end Ev

theorem norm_p (p : Nat.Primes) : ‖((p : ℕ) : ℂ_[p])‖ = ((p : ℕ) : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast (p := p), PadicComplex.norm_extends (p := p), ← PadicAlgCl.valuation_coe (p := p),
    PadicAlgCl.valuation_p]
  simp

theorem norm_p_lt_one (p : Nat.Primes) : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
  rw [norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)

theorem log_norm_cp {Ω : Type} [Field Ω] (R : Subring Ω) (p : Nat.Primes) (f : R →+* ℂ_[p]) {κ : Ω} (hκ : κ ∈ R)
    (h : HT.IsCp p κ) : f ⟨κ, hκ⟩ ≠ 0 ∧ Real.log ‖f ⟨κ, hκ⟩‖ = -(cP p * Real.log (p : ℕ)) := by
  have hp : (p : ℕ).Prime := p.2
  have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast hp.one_lt
  have key : ‖f ⟨κ, hκ⟩‖ = ((p : ℕ) : ℝ) ^ (-cP p) := by
    unfold HT.IsCp at h
    unfold cP
    split_ifs at h ⊢ with h2
    · have e : (⟨κ, hκ⟩ : R) = ((p : ℕ) : R) ^ 2 := Subtype.ext (by
        have e0 : κ = (((p : ℕ) : ℕ) : Ω) ^ 2 := by rw [h, h2]; norm_num
        simpa using e0)
      have hn := norm_p p
      rw [e, map_pow, map_natCast, norm_pow, hn, Real.rpow_neg (by positivity), inv_pow]
      norm_num
    · obtain ⟨ζ, hζ, rfl⟩ := h
      have hζR : ζ ∈ R := by simpa using R.add_mem hκ R.one_mem
      have hs : ∑ i ∈ Finset.range p, (⟨ζ, hζR⟩ : R) ^ i = 0 := Subtype.ext (by
        simpa using hζ.geom_sum_eq_zero hp.one_lt)
      have hs' : ∑ i ∈ Finset.range p, f ⟨ζ, hζR⟩ ^ i = 0 := by
        have := congrArg f hs
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_zero] at this
        simp only [map_pow] at this
        exact this
      have h1 : f ⟨ζ, hζR⟩ ≠ 1 := fun h1 => by
        rw [h1] at hs'
        simp at hs'
        exact hp.ne_zero hs'
      have hpow : f ⟨ζ, hζR⟩ ^ (p : ℕ) = 1 := by
        have := mul_geom_sum (f ⟨ζ, hζR⟩) p
        rw [hs', mul_zero] at this
        exact (sub_eq_zero.1 this.symm)
      have hprim : IsPrimitiveRoot (f ⟨ζ, hζR⟩) ((p : ℕ) ^ 1) := by
        rw [pow_one]
        have := IsPrimitiveRoot.orderOf (f ⟨ζ, hζR⟩)
        rwa [orderOf_eq_prime hpow h1] at this
      have e : f ⟨ζ - 1, hκ⟩ = f ⟨ζ, hζR⟩ - 1 := by
        rw [← map_one f, ← map_sub]; rfl
      rw [e, GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex p 1 le_rfl _ hprim]
      congr 1
      simp [neg_div]
  have hpos : 0 < ‖f ⟨κ, hκ⟩‖ := key ▸ Real.rpow_pos_of_pos (by positivity) _
  exact ⟨norm_pos_iff.1 hpos, by rw [key, Real.log_rpow (by positivity)]; ring⟩

section Line

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem wedge_of_span {n : ℕ} (b b₀ : Fin n → E) (h : flagStep Ω b n = flagStep Ω b₀ n) :
    ∃ α : Ω, exteriorPower.ιMulti Ω n b₀ = α • exteriorPower.ιMulti Ω n b := by
  have e : ∀ u : Fin n → E, flagStep Ω u n = Submodule.span Ω (Set.range u) := fun u => by
    unfold flagStep
    congr 1
    ext w
    simp
  have hm : ∀ i, ∃ t : Fin n → Ω, ∑ k, t k • b k = b₀ i := fun i => by
    have : b₀ i ∈ Submodule.span Ω (Set.range b) := by
      rw [← e, h, e]; exact Submodule.subset_span ⟨i, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun _).1 this
  choose t ht using hm
  refine ⟨(Matrix.of t).det, ?_⟩
  rw [← GlobalTheory.alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti Ω n (M := E)) (Matrix.of t) b]
  congr 1
  exact funext fun i => (ht i).symm

theorem coeff_order {A B : Lat ξ E} {p q : ℕ} {a : ⋀[Ω]^p E} {b : ⋀[Ω]^q E} {x : Cpt ξ} {bp : Fin p → E}
    {bq : Fin q → E} (hp : A.IsFrameAt bp x) (hq : B.IsFrameAt bq x) {α β : Ω} (hα : α ≠ 0) (hβ : β ≠ 0)
    (ea : a = α • exteriorPower.ιMulti Ω p bp) (eb : b = β • exteriorPower.ιMulti Ω q bq) {σ ϖ : Ω} {m : ℕ} {k : ℤ}
    (h : OrderAt (lineLat A B p q a b) σ ϖ m k x) : unitAt ξ x ((σ * α / β) ^ m / ϖ ^ k) := by
  obtain ⟨wp, np⟩ := GlobalTheory.T.wedge_lattice_generator X Ω ξ E A p bp x hp
  obtain ⟨wq, nq⟩ := GlobalTheory.T.wedge_lattice_generator X Ω ξ E B q bq x hq
  have hL : lineLat A B p q a b x = Submodule.span (regAt ξ x) {β / α} := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨f, ⟨α', β', hα', hβ', h1, h2, h3⟩, rfl⟩
      have m1 : α' • a ∈ Submodule.span (regAt ξ x) {exteriorPower.ιMulti Ω p bp} := by
        rw [← wp, h1]; exact Submodule.mem_span_singleton_self _
      have m2 : exteriorPower.ιMulti Ω q bq ∈ Submodule.span (regAt ξ x) {β' • b} := by
        rw [← h2, wq]; exact Submodule.mem_span_singleton_self _
      obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 m1
      obtain ⟨u', hu'⟩ := Submodule.mem_span_singleton.1 m2
      have e1 : (u : Ω) = α' * α := smul_left_injective Ω np (by
        change (u : Ω) • _ = (α' * α) • _
        rw [← smul_smul, ← ea]; exact hu)
      have e2 : (u' : Ω) * β' * β = 1 := smul_left_injective Ω nq (by
        change ((u' : Ω) * β' * β) • _ = (1 : Ω) • _
        rw [← smul_smul, ← smul_smul, ← eb, one_smul]; exact hu')
      refine Submodule.mem_span_singleton.2 ⟨u * u', ?_⟩
      change ((u : Ω) * u') * (β / α) = f⁻¹
      have e3 : f = β' / α' := eq_div_of_mul_eq hα' h3
      have e4 : (u' : Ω) = 1 / (β' * β) := eq_div_of_mul_eq (mul_ne_zero hβ' hβ) (by rw [← mul_assoc]; exact e2)
      rw [e1, e3, e4]
      field_simp
    · rintro _ rfl
      refine Submodule.subset_span ⟨α / β, ⟨α⁻¹, β⁻¹, inv_ne_zero hα, inv_ne_zero hβ, ?_, ?_, ?_⟩, (inv_div _ _).symm⟩
      · rw [wp, ea, smul_smul, inv_mul_cancel₀ hα, one_smul]
      · rw [wq, eb, smul_smul, inv_mul_cancel₀ hβ, one_smul]
      · field_simp
  obtain ⟨e, c, he, h1, h2, h3⟩ := h
  have m1 : e ∈ Submodule.span (regAt ξ x) {β / α} := by
    rw [← hL, h1]; exact Submodule.mem_span_singleton_self _
  have m2 : β / α ∈ Submodule.span (regAt ξ x) {e} := by
    rw [← h1, hL]; exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 m1
  obtain ⟨u', hu'⟩ := Submodule.mem_span_singleton.1 m2
  have hu1 : (u : Ω) * (β / α) = e := hu
  have hu2 : (u' : Ω) * e = β / α := hu'
  have huu : (u : Ω) * u' = 1 := mul_right_cancel₀ he (by rw [mul_assoc, hu2, hu1, one_mul])
  have hunit : unitAt ξ x (u : Ω) :=
    ⟨left_ne_zero_of_mul_eq_one huu, u.2, by rw [← eq_inv_of_mul_eq_one_right huu]; exact u'.2⟩
  have e5 : σ * α / β = c * u := by
    rw [h2, smul_eq_mul, ← hu1]
    field_simp
  rw [e5, mul_pow, mul_div_right_comm]
  exact ZUnit.mul h3 (ZUnit.pow hunit m)

end Line

end RootFieldNumerics.RF.Loc
end
end

