module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetC
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

variable {g : ℕ} {Y Y' : Scheme.{0}}

theorem valAt'_comp (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Y') (U : Y'.Opens) (f : Γ(Y', U)) :
    valAt' x (φ ⁻¹ᵁ U) (φ.app U f) = valAt' (x ≫ φ) U f := by
  unfold valAt'
  have e : x ⁻¹ᵁ φ ⁻¹ᵁ U = (x ≫ φ) ⁻¹ᵁ U := rfl
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · rw [dite_eq_left (e ▸ h), dite_eq_left h]
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · rw [dite_eq_right (e ▸ h), dite_eq_right h]

theorem isHolFam_comp (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (φ : Y ⟶ Y') :
    IsHolFam (fun z => e z ≫ φ) := by
  intro U f
  have := hol (φ ⁻¹ᵁ U) (φ.app U f)
  simp only [valAt'_comp] at this
  exact this


set_option backward.isDefEq.respectTransparency false in
theorem jetPt_comp (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (φ : Y ⟶ Y')
    (e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y')) (hol' : IsHolFam e') (he : ∀ z, e z ≫ φ = e' z) (m : ℕ) :
    jetPt e hol m ≫ φ = jetPt e' hol' m := by
  have hpt : (jetPt e hol m ≫ φ) (IsLocalRing.closedPoint _) = jetPt e' hol' m (IsLocalRing.closedPoint _) := by
    rw [Scheme.Hom.comp_apply, jetPt_closedPoint, jetPt_closedPoint, ← he 0, Scheme.Hom.comp_apply]
  refine hom_ext_of_local hpt fun U h₁ h₂ => ?_
  have hU : e' 0 cpt ∈ U := by
    have : jetPt e' hol' m (IsLocalRing.closedPoint _) ∈ U :=
      h₂ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [jetPt_closedPoint] at this
  have hU' : φ (e 0 cpt) ∈ U := by
    rw [← Scheme.Hom.comp_apply, he 0]; exact hU
  have k := nbhdPt_comp_appLE (y₀ := e 0 cpt) φ (jetψ e hol m) (jetψ_res e hol m) (jetψ_loc e hol m) U hU' h₁
  refine (k : (jetPt e hol m ≫ φ).appLE U ⊤ h₁ = _).trans ?_
  rw [jetPt_appLE e' hol' m U hU h₂, ← Category.assoc]
  congr 1
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  congr 1
  funext z
  rw [valAt'_comp, he z]


set_option backward.isDefEq.respectTransparency false in
theorem jetPt_aug (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ) :
    spMap ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) ≫ jetPt e hol m = e 0 := by
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  have hloc : ∀ (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)),
      IsUnit ((jetψ e hol m U hU ≫ CommRingCat.ofHom
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ)) f) →
        e 0 cpt ∈ Y.basicOpen f := by
    intro U hU f hf
    rw [CommRingCat.comp_apply, jetψ_apply] at hf
    change IsUnit ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) _) at hf
    rw [jetAug_jetOf] at hf
    exact (valAt'_ne_zero_iff (e 0) U (top_le_of_mem hU) f cpt).mp hf.ne_zero
  have hres : ∀ (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ (jetψ e hol m V hV ≫ CommRingCat.ofHom
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ)) =
      jetψ e hol m U hU ≫ CommRingCat.ofHom
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) :=
    fun U V hU hV h => by rw [← Category.assoc, jetψ_res]
  have hpt := nbhdPt_closedPoint _ hres hloc
  refine hom_ext_of_local (hpt.trans rfl) fun U h₁ h₂ => ?_
  have hU : e 0 cpt ∈ U := by
    have : nbhdPt _ hres (IsLocalRing.closedPoint _) ∈ U :=
      h₁ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [hpt] at this
  rw [nbhdPt_appLE _ hres hloc U hU h₁, Iso.comp_inv_eq]
  ext f
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, jetψ_apply]
  change (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) _ = _
  rw [jetAug_jetOf, valAt'_of _ _ h₂]
  rfl

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TcoordJetLin
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD

open MvPolynomial CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Formalism.L2.Pj
  ReciprocityTheory.ChartRestriction.G

attribute [local instance] Over.cartesianMonoidalCategory

variable {V : Type} [CommRing V] {d : ℕ}

theorem tcoord_jet_lin {n : ℕ} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
    {x : ∀ m, Chart.sp (R₀ := V) (Chart.JetR V (Fin n) m) ⟶ G} (hx : Chart.IsUnivChart G n x)
    (y : Chart.sp (R₀ := V) (Jet V (Fin 1 × Fin d) 1) ⟶ G)
    (hy : Chart.spMap ((jetAug : Jet V (Fin 1 × Fin d) 1 →ₐ[V] V)) ≫ y = 1)
    (φ : Jet V (Fin 1 × Fin d) 1 →ₐ[V] DualNumber V) (hφ : ∀ w, (φ w).fst = jetAug w)
    (h : Chart.IsTan (Chart.spMap φ ≫ y))
    (hk : ∀ k : Fin d, Chart.IsTan (Chart.spMap (jetTan (R := V) (m := 0) ((0 : Fin 1), k)) ≫ y)) :
    Chart.tcoord hx _ h = ∑ k, (φ (zk k)).snd • Chart.tcoord hx _ (hk k) := by
  obtain ⟨ψ, ⟨hψa, hψy⟩, -⟩ := hx.2.2 (Jet V (Fin 1 × Fin d) 1) jetAug 1 ker_jetAug_sq y hy
  have key : ∀ (χ : Jet V (Fin 1 × Fin d) 1 →ₐ[V] DualNumber V), (∀ w, (χ w).fst = jetAug w) →
      ∀ hχ : Chart.IsTan (Chart.spMap χ ≫ y),
        Chart.tcoord hx _ hχ = fun j => (χ (ψ (Chart.zR 1 j))).snd := by
    intro χ hχf hχ
    apply Chart.tcoord_eq
    have hc : (Chart.fstD V).comp (χ.comp ψ) = Chart.jetAug V (Fin n) 1 := by
      refine AlgHom.ext fun a => ?_
      have h1 := hχf (ψ a)
      have h2 := AlgHom.congr_fun hψa a
      simp only [AlgHom.comp_apply] at h2 ⊢
      exact h1.trans h2
    rw [hψy, ← Category.assoc, Chart.spMap_comp]
    exact congrArg (fun f => Chart.spMap f ≫ x 1) (Chart.eq_dualLift (χ.comp ψ) hc)
  have hk' : ∀ k, Chart.tcoord hx _ (hk k) =
      fun j => (jetTan (R := V) (m := 0) ((0 : Fin 1), k) (ψ (Chart.zR 1 j))).snd :=
    fun k => key _ (fst_jetTan k) (hk k)
  rw [key φ hφ h]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hk']
  exact snd_lin φ hφ (ψ (Chart.zR 1 j))

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
end
end

