module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDepthLowerBoundSaturatedEvenType
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVarietyCompactifyingConnectedComponent
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.CompactVar

theorem geometricallyConnected_of_denseRange {F : Type} [Field F] {U V : Scheme.{0}} (g : U ⟶ V) (p : V ⟶ Sp F)
    (hg : Dense (Set.range g)) [GeometricallyConnected (g ≫ p)] : GeometricallyConnected p := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have h1 : ConnectedSpace ↥(pullback (g ≫ p) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  rw [← (pullbackRightPullbackFstIso p x g).hom.homeomorph.connectedSpace_iff] at h1
  have ho : UniversallyOpen x := inferInstance
  have h2 : Dense (Set.range (pullback.snd g (pullback.fst p x))) := by
    rw [Scheme.Pullback.range_snd]
    exact hg.preimage (pullback.fst p x).isOpenMap
  rw [connectedSpace_iff_univ, ← h2.closure_eq]
  exact (isConnected_range (Scheme.Hom.continuous _)).closure

theorem exists_var : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens), SmoothOfRelativeDimension D.dim (genStr Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → ∃ (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsOpenImmersion io ∧ Set.range io = compactOf Y U ∧ io ≫ genStr Y = B.str := by
  intro E _ _ _ H D l Xo c O _ β Z U hsm _ hU
  have hS : Smooth (genStr Z) := SmoothOfRelativeDimension.smooth D.dim _
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  have := Z.jQ_open
  have hcc := fun z : gen Z => GlobalTheory.ShFam.PtComp.connectedComponent_mem
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => GlobalTheory.ShFam.PtComp.disjoint_of_smooth (genStr Z) hS W W' hW hW') z
  have hconn : ConnectedSpace U.toScheme :=
    GeometricallyConnected.connectedSpace_of_subsingleton (U.ι ≫ toF Xo c)
  let π : U.toScheme ⟶ gen Z := U.ι ≫ Z.jQ
  have hπ : Set.range π = Z.jQ '' U := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  let z : gen Z := π (Classical.arbitrary _)
  let V : (gen Z).Opens := ⟨connectedComponent z, (hcc z).2⟩
  have hred : IsReduced (gen Z) := by
    have := GlobalTheory.isNormalScheme_of_smooth (genStr Z)
    exact GlobalTheory.IsNormalScheme.isReduced
  have hproj : IsProjOver (genStr Z) := (GlobalTheory.ProjSpace.points_and_stability (R := O) (N := 0)).2.2.1 c.F β Z.X Z.s Z.proj
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace (hcc z).1.1
  have hcl : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
  have hp : IsProjOver (V.ι ≫ genStr Z) :=
    (GlobalTheory.ProjSpace.points_and_stability (R := c.F) (N := 0)).2.2.2.1 _ _ _ _ hcl hproj
  have hsd : SmoothOfRelativeDimension D.dim (V.ι ≫ genStr Z) := by
    have h : SmoothOfRelativeDimension (0 + D.dim) (V.ι ≫ genStr Z) := inferInstance
    simpa using h
  have hr : Set.range π ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact (isPreconnected_range π.continuous).subset_connectedComponent ⟨_, rfl⟩
  let g : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι π hr
  have hg : g ≫ V.ι = π := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (g ≫ V.ι) := by rw [hg]; infer_instance
  have : IsOpenImmersion g := IsOpenImmersion.of_comp g V.ι
  have hd : Dense (Set.range g) := g.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  have : GeometricallyConnected (g ≫ V.ι ≫ genStr Z) := by
    rw [reassoc_of% hg, Category.assoc, Z.jQ_over]
    exact hU
  have : GeometricallyConnected (V.ι ≫ genStr Z) := geometricallyConnected_of_denseRange g _ hd
  obtain ⟨X, ε, -, hs⟩ := GlobalTheory.ProjVar.Var.exists_iso _ D.dim hp
  refine ⟨X, ε.inv ≫ V.ι, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ε.inv.surjective.range_eq, Set.image_univ,
      compactOf, ← hπ, ← hg, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      V.ι.isClosedEmbedding.closure_image_eq, hd.closure_eq, Set.image_univ]
  · rw [Category.assoc, ← hs, Iso.inv_hom_id_assoc]

end GlobalTheory.CompactVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldImageOpenImmersion
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LogKS.FieldImage

variable {Z Z' : Scheme.{0}} (φ : Z' ⟶ Z) [IsOpenImmersion φ]

def appEquiv (O : Z.Opens) (h : O ≤ φ.opensRange) : Γ(Z, O) ≃+* Γ(Z', φ ⁻¹ᵁ O) :=
  haveI := Scheme.Hom.isIso_app φ O h
  (asIso (φ.app O)).commRingCatIsoToRingEquiv

theorem appEquiv_apply (O : Z.Opens) (h : O ≤ φ.opensRange) (f : Γ(Z, O)) :
    appEquiv φ O h f = (φ.app O).hom f := rfl

theorem app_res {W W' : Z.Opens} (h : W' ≤ W) (f : Γ(Z, W)) :
    (φ.app W').hom (resG Z h f) = resG Z' (Scheme.Hom.preimage_mono φ h) ((φ.app W).hom f) := by
  have := congrArg (fun g => g.hom f) (Scheme.Hom.naturality φ (homOfLE h).op)
  simpa [resG] using this


open Classical in
def push (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (O : Z.Opens) (f : Γ(Z, O)) : Γ(Z, O) :=
  if h : O ≤ φ.opensRange then (appEquiv φ O h).symm (d (φ ⁻¹ᵁ O) ((φ.app O).hom f)) else 0

theorem app_push (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (O : Z.Opens) (h : O ≤ φ.opensRange)
    (f : Γ(Z, O)) : (φ.app O).hom (push φ d O f) = d (φ ⁻¹ᵁ O) ((φ.app O).hom f) := by
  rw [push, dite_eq_left h, ← appEquiv_apply φ O h, RingEquiv.apply_symm_apply]

theorem le_range {W₀ : Z'.Opens} {O : Z.Opens} (hO : O ≤ φ ''ᵁ W₀) : O ≤ φ.opensRange :=
  hO.trans (Scheme.Hom.image_le_opensRange φ W₀)

theorem preimage_le {W₀ : Z'.Opens} {O : Z.Opens} (hO : O ≤ φ ''ᵁ W₀) : φ ⁻¹ᵁ O ≤ W₀ := by
  have := Scheme.Hom.preimage_mono φ hO
  rwa [Scheme.Hom.preimage_image_eq] at this

theorem inj_app {O : Z.Opens} (h : O ≤ φ.opensRange) : Function.Injective (φ.app O).hom :=
  (appEquiv φ O h).injective

theorem isField_push (W₀ : Z'.Opens) (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (hd : IsField W₀ d) :
    IsField (φ ''ᵁ W₀) (push φ d) := by
  obtain ⟨hadd, hmul, hres⟩ := hd
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
  · apply inj_app φ (le_range φ hW)
    rw [map_add (f := _), app_push φ d W (le_range φ hW), app_push φ d W (le_range φ hW),
      app_push φ d W (le_range φ hW), map_add, hadd _ (preimage_le φ hW)]
  · apply inj_app φ (le_range φ hW)
    rw [map_add (f := _), map_mul, map_mul, app_push φ d W (le_range φ hW), app_push φ d W (le_range φ hW),
      app_push φ d W (le_range φ hW), map_mul, hmul _ (preimage_le φ hW)]
  · have hW' : W' ≤ φ ''ᵁ W₀ := h.trans hW
    apply inj_app φ (le_range φ hW')
    rw [app_push φ d W' (le_range φ hW'), app_res, app_res, app_push φ d W (le_range φ hW),
      hres _ _ _ (preimage_le φ hW)]

end GlobalTheory.LogKS.FieldImage

theorem GlobalTheory.LogKS.isField_image : ∀ (Z Z' : Scheme.{0}) (φ : Z' ⟶ Z) [IsOpenImmersion φ] (W₀ : Z'.Opens) (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)), IsField W₀ d → ∃ d₂ : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField (φ ''ᵁ W₀) d₂ ∧ ∀ (O : Z.Opens), O ≤ φ ''ᵁ W₀ → ∀ f : Γ(Z, O), (φ.app O).hom (d₂ O f) = d (φ ⁻¹ᵁ O) ((φ.app O).hom f) := by
  intro Z Z' φ _ W₀ d hd
  exact ⟨FieldImage.push φ d, FieldImage.isField_push φ W₀ d hd,
    fun O hO f => FieldImage.app_push φ d O (FieldImage.le_range φ hO) f⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorGroupDeterminantsNeZero
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericGroupDet

theorem det_delta_ne_zero (S : Type) [Group S] [Fintype S] [DecidableEq S] (f : S → ℂ)
    (hf : ∀ h, f h = if h = 1 then 1 else 0) :
    (Matrix.of fun h g : S => f (h * g)).det ≠ 0 := by
  have : (Matrix.of fun h g : S => f (h * g)) = (Equiv.inv S).permMatrix ℂ := by
    ext h g
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hf, mul_eq_one_iff_inv_eq]
  rw [this, Matrix.det_permutation]
  simp

theorem exists_combination_delta (F V S J : Type) [Field F] [Algebra F ℂ] [AddCommGroup V] [Module F V]
    [Group S] [Fintype S] [DecidableEq S] [Fintype J]
    (ev : V →ₗ[F] (S → ℂ)) (r : J → S) (W : Submodule F V) (h1 : ∃ j, r j = 1)
    (h2 : ∀ v ∈ W, ∀ h, h ∉ Set.range r → ev v h = 0)
    (h3 : ∀ a : J → ℂ, (∀ v ∈ W, ∑ j, a j * ev v (r j) = 0) → a = 0) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → V), (∀ k, w k ∈ W) ∧
      ∀ h, ∑ k, c k * ev (w k) h = if h = 1 then 1 else 0 := by
  classical
  set s : Set (J → ℂ) := (fun v => fun j => ev v (r j)) '' (W : Set V) with hs
  have htop : Submodule.span ℂ s = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hφ : ∀ x : J → ℂ, φ x = ∑ j, x j * φ (fun j' => if j = j' then 1 else 0) := fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      simp [smul_eq_mul]
    have ha := h3 (fun j => φ (fun j' => if j = j' then 1 else 0)) fun v hv => by
      have := hle (Submodule.subset_span ⟨v, hv, rfl⟩)
      rw [LinearMap.mem_ker, hφ] at this
      simpa [mul_comm] using this
    apply hφ0
    refine LinearMap.ext fun x => ?_
    rw [hφ x, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [congrFun ha j]; simp
  let b : J → ℂ := fun j => if r j = 1 then 1 else 0
  have hb : b ∈ Submodule.span ℂ s := htop ▸ Submodule.mem_top
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hb
  choose w hw hwg using fun k => (g k).2
  refine ⟨n, c, w, hw, fun h => ?_⟩
  by_cases hr : h ∈ Set.range r
  · obtain ⟨j, rfl⟩ := hr
    have := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hwg k]
  · have h1' : h ≠ 1 := by
      rintro rfl
      obtain ⟨j, hj⟩ := h1
      exact hr ⟨j, hj⟩
    rw [if_neg h1']
    exact Finset.sum_eq_zero fun k _ => by rw [h2 _ (hw k) h hr, mul_zero]

theorem exists_vec_det_ne_zero (F : Type) [Field F] [CharZero F] [Algebra F ℂ] (V : Type) [AddCommGroup V] [Module F V]
    (S : Type) [Group S] [Fintype S] [DecidableEq S] (ι : Type) [Finite ι] (ev : ι → V →ₗ[F] (S → ℂ))
    (J : ι → Type) [∀ i, Fintype (J i)] (r : ∀ i, J i → S) (W : ι → Submodule F V)
    (h1 : ∀ i, ∃ j, r i j = 1) (h2 : ∀ i, ∀ v ∈ W i, ∀ h, h ∉ Set.range (r i) → ev i v h = 0)
    (h3 : ∀ i (a : J i → ℂ), (∀ v ∈ W i, ∑ j, a j * ev i v (r i j) = 0) → a = 0) :
    ∃ v : V, ∀ i, (Matrix.of fun h g : S => ev i v (h * g)).det ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  choose n c w hw hcw using fun i => exists_combination_delta F V S (J i) (ev i) (r i) (W i) (h1 i) (h2 i) (h3 i)
  let vec : (Σ i, Fin (n i)) → V := fun p => w p.1 p.2
  let P : ι → MvPolynomial (Σ i, Fin (n i)) ℂ := fun i =>
    Matrix.det (Matrix.of fun h g : S => ∑ p, MvPolynomial.X p * MvPolynomial.C (ev i (vec p) (h * g)))
  have hP : ∀ i (x : (Σ i, Fin (n i)) → ℂ), MvPolynomial.eval x (P i) =
      (Matrix.of fun h g : S => ∑ p, x p * ev i (vec p) (h * g)).det := by
    intro i x
    rw [RingHom.map_det]
    congr 1
    ext h g
    simp [RingHom.mapMatrix_apply]
  have hPi : ∀ i, P i ≠ 0 := by
    intro i hz
    let x : (Σ i, Fin (n i)) → ℂ := fun p => if p.1 = i then c p.1 p.2 else 0
    have hx : ∀ h, ∑ p, x p * ev i (vec p) h = if h = 1 then 1 else 0 := by
      intro h
      rw [← hcw i h, Fintype.sum_sigma, Finset.sum_eq_single i]
      · simp [x, vec]
      · intro b _ hb
        exact Finset.sum_eq_zero fun k _ => by simp [x, hb]
      · simp
    have := det_delta_ne_zero S _ hx
    rw [← hP, hz, map_zero] at this
    exact this rfl
  have hQ : (∏ i, P i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hPi i
  obtain ⟨x, hx, hQx⟩ : ∃ x ∈ Set.pi Set.univ (fun _ : (Σ i, Fin (n i)) => Set.range (algebraMap F ℂ)),
      MvPolynomial.eval x (∏ i, P i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ (MvPolynomial.funext_set (fun _ => Set.range (algebraMap F ℂ))
      (fun _ => Set.infinite_range_of_injective (algebraMap F ℂ).injective)
      fun x hx => by rw [hcon x hx, map_zero])
  choose t ht using fun p => hx p (Set.mem_univ p)
  refine ⟨∑ p, t p • vec p, fun i => ?_⟩
  have hne : MvPolynomial.eval x (P i) ≠ 0 := by
    rw [map_prod] at hQx
    exact Finset.prod_ne_zero_iff.1 hQx i (Finset.mem_univ _)
  rw [hP] at hne
  convert hne using 2
  ext h g
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Finset.sum_apply, Algebra.smul_def, ht]

end GlobalTheory.GenericGroupDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBoundedOddInertPrimeCmType
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem inPsi_orbit_parity {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {h : ℕ}
    (hh : 0 < h) (lab : ZMod h → (E →+* ℂ)) (hstep : ∀ s, InPsi H (lab (s + 1)) ↔ ¬ InPsi H (lab s))
    (h0 : InPsi H (lab 0)) : Even h ∧ ∀ s : ZMod h, InPsi H (lab s) ↔ Even s.val := by
  have hn : ∀ n : ℕ, InPsi H (lab (n : ZMod h)) ↔ Even n := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [Nat.cast_succ, hstep, ih, Nat.even_add_one]
  haveI : NeZero h := ⟨hh.ne'⟩
  refine ⟨(hn h).1 (by simpa [ZMod.natCast_self] using h0), fun s => ?_⟩
  have := hn s.val
  rwa [ZMod.natCast_zmod_val] at this

theorem facBetween_fine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), p ≠ 2 → ¬ (p : ℤ) ∣ discr E → InertInK H p → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → 1 ≤ k → ∃ A B : ℝ, FacBetween Xo la f k A B ∧ B - A ≤ boundFine p (Dw.p + Dw.q) Dw.q (rk f) k := by
  intro E _ _ _ H Dw l Xo c p _ la hp2 hdisc hin f k hf hk
  letI := H.starRing
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpp : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hL : 0 ≤ Real.logb p k := Real.logb_nonneg hp1 (by exact_mod_cast hk)
  refine ⟨((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p / ((p : ℝ) ^ 2 - 1) - (rk f : ℝ) ^ 2 * (Real.logb p k + 1),
    k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)), ?_, ?_⟩
  · intro T io e ho y
    refine ⟨le_nuFac fun Ch X => ?_, fun halg =>
      (GlobalTheory.T.factorDepth_upperBound_oddUnramifiedPrime E H Dw l Xo c p T io y (not_isUnit_of_overLa la ho) halg hp2 hdisc f k hf).2 hin⟩
    obtain ⟨hfrob, hty⟩ := _root_.GlobalTheory.PrimePart.formalGroupTypes E H Dw l Xo c (fun _ => rfl) p hdisc T io X
    obtain ⟨h, hh0, -, lab, horb, d', G', ty, I, P, -, ⟨mu⟩, -, hcard, hfr⟩ := hty y Ch f.1
    have hstep : ∀ s, InPsi H (lab (s + 1)) ↔ ¬ InPsi H (lab s) := by
      intro s
      rw [((hfrob _ _ (horb.2.1 s)).2 hin)]
      constructor
      · intro h1 h2
        exact ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.not_inPsi_both H (lab s) ⟨h2, h1⟩
      · intro h1
        exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H (lab s)).resolve_left h1
    obtain ⟨hev, hpar⟩ := inPsi_orbit_parity hh0 lab hstep (by rw [horb.1]; exact hf)
    have hodd : ∀ s : ZMod h, Odd s.val → (Finset.univ.filter fun a => ty a = s).card ≤ Dw.q := by
      intro s hs
      have hn : ¬ InPsi H (lab s) := fun h1 => (Nat.not_even_iff_odd.2 hs) ((hpar s).1 h1)
      have h2 := hcard s
      rw [if_neg hn] at h2
      rw [← h2, Fintype.card_subtype]
    obtain ⟨hsat, hzero, hdep⟩ := hfr 0 f horb.1.symm
    obtain ⟨cr, -, hcr, hlow⟩ := _root_.GlobalTheory.DepthLow.detDepth_lower X.C (vX_vp X) p hp (vX_vp_p X) hp3 d' h hh0 hev ty G' mu Dw.q hodd
      (0 : ZMod h) (by simp) (rk f) k hk (fun a => P.mulVec (frame Ch X f a)) hsat hzero
    rw [nuFacC, ← hdep] at *
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) hlow
    have h3 : ((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p ≤ ((rk f : ℝ) - cr) * k * p := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have h4 := div_le_div_of_nonneg_right h3 hpp.le
    linarith
  · have hab : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 1 / ((p : ℝ) - 1) := by
      rw [div_le_div_iff₀ hpp (by linarith)]
      nlinarith
    have hkey : boundFine p (Dw.p + Dw.q) Dw.q (rk f) k -
        (k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)) -
          (((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p / ((p : ℝ) ^ 2 - 1) - (rk f : ℝ) ^ 2 * (Real.logb p k + 1))) =
        (k : ℝ) * Dw.q * (1 / 2 * (1 / ((p : ℝ) - 1)) + (3 / 2 + Real.logb p k / 2) * (1 / ((p : ℝ) - 1) - (p : ℝ) / ((p : ℝ) ^ 2 - 1))) := by
      unfold boundFine
      push_cast
      ring
    have hpos : 0 ≤ (k : ℝ) * Dw.q * (1 / 2 * (1 / ((p : ℝ) - 1)) + (3 / 2 + Real.logb p k / 2) * (1 / ((p : ℝ) - 1) - (p : ℝ) / ((p : ℝ) ^ 2 - 1))) := by
      have hb : 0 ≤ 1 / ((p : ℝ) - 1) := by apply div_nonneg <;> linarith
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ 3 / 2 + Real.logb p k / 2) (sub_nonneg.2 hab)
      positivity
    linarith

end GlobalTheory.RefSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevelBis
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section


open GlobalTheory.BCT.StabFin in
theorem GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev_anyRank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU (E := E) (n := n), Finite (ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom : Subgroup (finU (E := E) (n := n))) := by
  intro E _ _ _ _ n S hS K' hK x
  obtain ⟨d, hd, hC⟩ := GlobalTheory.T.exists_bounded_denominator_definiteUnitary_conjugate E n S hS x
  haveI : Finite {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈
      w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1} := (_root_.GlobalTheory.NumFin.finite_bdd_denom_conj_le_one E d hd).to_subtype
  have hrat := (GlobalTheory.BCT.FinPart.finPt_props E n).2.2
  let γ : ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) → UE E n :=
    fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose
  have hγ : ∀ g, finPt (γ g) = g.1 := fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose_spec
  refine Finite.of_injective (β := Fin n → Fin n → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) *
      algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1})
    (fun g i j => ⟨((γ g : UE E n) : GL (Fin n) E).val i j, fun w => by
        have := hC g.1 (cLoc_conj_mem_KGL hK x g.1 (Subgroup.mem_inf.1 g.2).2) w i j
        rwa [← hγ g, cLoc_finPt] at this,
      fun τ => _root_.GlobalTheory.BCT.FinPart.norm_emb_entry_le_one E n (γ g) τ i j⟩) fun g g' e => ?_
  have e1 : γ g = γ g' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact congrArg Subtype.val (congrFun (congrFun e i) j)
  apply Subtype.ext
  rw [← hγ g, ← hγ g', e1]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceTwistedComplexificatio
section
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.DefRead

theorem bcLin_sub_smul_apply {K W : Type} [Field K] [AddCommGroup W] [Module K W] (σ : K →+* ℂ)
    (f : W →ₗ[K] W) (a : K) (v : VC σ W) :
    bcLin σ (f - a • LinearMap.id) v = bcLin σ f v - σ a • v := by
  letI : Algebra K ℂ := σ.toAlgebra
  revert v
  show ∀ v : ℂ ⊗[K] W, LinearMap.baseChange ℂ (f - a • LinearMap.id) v = LinearMap.baseChange ℂ f v - σ a • v
  intro v
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_id]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  congr 1

theorem bcLin_sum_smul {K W G : Type} [Field K] [AddCommGroup W] [Module K W] [Fintype G] (σ : K →+* ℂ)
    (f : G → W →ₗ[K] W) (a : G → K) :
    bcLin σ (∑ g, a g • f g) = ∑ g, σ (a g) • bcLin σ (f g) := by
  letI : Algebra K ℂ := σ.toAlgebra
  show LinearMap.baseChangeHom K ℂ W W (∑ g, a g • f g) = ∑ g, σ (a g) • LinearMap.baseChange ℂ (f g)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  show LinearMap.baseChange ℂ (a g • f g) = _
  rw [LinearMap.baseChange_smul]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, ← algebraMap_smul ℂ (a g)]
  rfl

end GlobalTheory.DefRead

namespace GlobalTheory.DefRead

theorem finrank_eig_twBC : ∀ (K W G : Type) [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Group G] [Fintype G]
    (σ : K →+* ℂ) (ρ0 : G →* (W →ₗ[K] W)) (χ : G →* Kˣ) (J : Subgroup G) (μ : J →* Kˣ) (c : G → K),
    Module.finrank K (⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ)) ∧
    Module.finrank K ((⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id)) ⊓
        LinearMap.ker (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ) ⊓
        LinearMap.ker (Representation.asAlgebraHom (GlobalTheory.DefRead.twBC σ ρ0 χ) (∑ g, MonoidAlgebra.single g (σ (c g)))) :
          Submodule ℂ (GlobalTheory.DefRead.VC σ W)) := by
  intro K W G _ _ _ _ _ _ σ ρ0 χ J μ c
  letI : Algebra K ℂ := σ.toAlgebra
  set a : J → W →ₗ[K] W := fun p => ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id with ha
  have hker : ∀ p : J, LinearMap.ker (twBC σ ρ0 χ (p : G) -
      ((((Units.map σ.toMonoidHom).comp μ) p : ℂˣ) : ℂ) • LinearMap.id) = LinearMap.ker (bcLin σ (a p)) := by
    intro p
    ext v
    have hμ : ((((Units.map σ.toMonoidHom).comp μ) p : ℂˣ) : ℂ) = σ (μ p) := rfl
    have hu : σ (((χ p)⁻¹ : Kˣ) : K) * σ ((χ p * μ p : Kˣ) : K) = σ (μ p) := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel_left]
    have hu0 : σ (((χ p)⁻¹ : Kˣ) : K) ≠ 0 := (map_ne_zero σ).2 (Units.ne_zero _)
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ha, bcLin_sub_smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, twBC_apply, LinearMap.smul_apply, hμ, ← hu, ← smul_smul, ← smul_sub, smul_eq_zero,
      or_iff_right hu0]
  have heig : eig (twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ) = ⨅ p : J, LinearMap.ker (bcLin σ (a p)) :=
    iInf_congr hker
  have halg : Representation.asAlgebraHom (twBC σ ρ0 χ) (∑ g, MonoidAlgebra.single g (σ (c g))) =
      bcLin σ (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, bcLin_sum_smul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Representation.asAlgebraHom_single, twBC_apply, smul_smul, map_mul]
  have hbc := TensorProduct.isBaseChange K W ℂ
  have h1 := finrank_iInf_ker_baseChange K ℂ W (ℂ ⊗[K] W) J (TensorProduct.mk K ℂ W 1) hbc a
    (fun p => (bcLin σ (a p) : ℂ ⊗[K] W →ₗ[ℂ] ℂ ⊗[K] W)) (fun p v => complexificationBaseChangeLinear_one_tmul σ (a p) v)
  set b : Option J → W →ₗ[K] W := fun o => o.elim (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) a with hb
  have h2 := finrank_iInf_ker_baseChange K ℂ W (ℂ ⊗[K] W) (Option J) (TensorProduct.mk K ℂ W 1) hbc b
    (fun o => (bcLin σ (b o) : ℂ ⊗[K] W →ₗ[ℂ] ℂ ⊗[K] W)) (fun o v => complexificationBaseChangeLinear_one_tmul σ (b o) v)
  rw [iInf_option, iInf_option] at h2
  refine ⟨?_, ?_⟩
  · rw [heig]
    exact h1.1.symm
  · rw [heig, halg, inf_comm]
    conv_rhs => rw [inf_comm]
    exact h2.1.symm

end GlobalTheory.DefRead
end

