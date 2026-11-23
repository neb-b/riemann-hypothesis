module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorSchemeLineBundleAffineFiniteType
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace GenAffine

open GeneratorFunctor

set_option backward.isDefEq.respectTransparency false

theorem exists_torus_one (S : Scheme.{0}) :
    ∃ (T : Scheme.{0}) (p : T ⟶ S) (t : Γ(T, ⊤)ˣ), IsAffineHom p ∧ LocallyOfFiniteType p ∧
      (∀ (Z : Scheme.{0}) (c : Z ⟶ S) (v : Γ(Z, ⊤)ˣ), ∃ g : Z ⟶ T, g ≫ p = c ∧
        g.appTop.hom t.val = v.val) ∧
      ∀ (Z : Scheme.{0}) (g g' : Z ⟶ T), g ≫ p = g' ≫ p →
        g.appTop.hom t.val = g'.appTop.hom t.val → g = g' := by
  refine ⟨(splitTorus S ℤ).left, (splitTorus S ℤ).hom, charUnit S ℤ 1, inferInstance,
    inferInstance, fun Z c v => ?_, fun Z g g' h hk => ?_⟩
  · let φ : ℤ →+ Additive Γ(Z, ⊤)ˣ := zmultiplesHom _ (Additive.ofMul v)
    obtain ⟨g, hg⟩ := (splitTorusPointsEquiv S ℤ (Over.mk c)).surjective
      (AddMonoidHom.toMultiplicativeLeft φ)
    refine ⟨g.left, Over.w g, ?_⟩
    refine (splitTorusPointsEquiv_val S _ (Over.mk c) g _).symm.trans ?_
    rw [hg]
    simp [φ]
  · let Z' : Over S := Over.mk (g' ≫ (splitTorus S ℤ).hom)
    let a : Z' ⟶ splitTorus S ℤ := Over.homMk g h
    let a' : Z' ⟶ splitTorus S ℤ := Over.homMk g' rfl
    have : a = a' := by
      apply (splitTorusPointsEquiv S ℤ Z').injective
      apply AddMonoidHom.toMultiplicativeLeft.symm.injective
      refine AddMonoidHom.ext_int ?_
      apply Additive.toMul.injective
      apply Units.ext
      exact ((splitTorusPointsEquiv_val S _ Z' a _).trans hk).trans
        (splitTorusPointsEquiv_val S _ Z' a' _).symm
    exact congrArg (·.left) this

theorem pb_inv_val {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (W : Z.Opens) (h : W ≤ f ⁻¹ᵁ U)
    (x : Γ(Y, U)ˣ) : (f.appLE U W h).hom (x⁻¹).val = ((pb f U W h x)⁻¹).val := by
  rw [← map_inv, pb_val]

end GenAffine


set_option backward.isDefEq.respectTransparency false in
open GeneratorFunctor GenAffine Opposite in
theorem generatorScheme_affine_finiteType : ∀ (B : Scheme.{0}) (N : LB B), N.IsLB → ∃ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ i : N.ι, Γ(G, q ⁻¹ᵁ N.U i)ˣ), IsAffineHom q ∧ LocallyOfFiniteType q ∧ (∀ i i', res (Scheme.Hom.preimage_mono q (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (u i) = pullU q _ (N.g i i') * res (Scheme.Hom.preimage_mono q (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (u i')) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ i : N.ι, Γ(Z, b ⁻¹ᵁ N.U i)ˣ), (∀ i i', res (Scheme.Hom.preimage_mono b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (s i) = pullU b _ (N.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (s i')) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ i, (g.appLE (q ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl)).hom (u i).val = (s i).val := by
  intro B N hN
  obtain ⟨G, ⟨e⟩⟩ := (isRepresentable_genFunctor (N := fun _ : Unit => N) fun _ => hN).has_representation
  let x : Pt (fun _ : Unit => N) G := e.homEquiv (𝟙 G)
  have he : ∀ {Z : Scheme.{0}} (g : Z ⟶ G), e.homEquiv g = Pt.map g x := fun g => by
    rw [e.homEquiv_eq]; rfl
  have hinj : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ G), Pt.map g x = Pt.map g' x → g = g' :=
    fun g g' h => e.homEquiv.injective (by rw [he, he]; exact h)
  have hsurj : ∀ {Z : Scheme.{0}} (y : Pt (fun _ : Unit => N) Z), ∃ g : Z ⟶ G, Pt.map g x = y :=
    fun y => ⟨e.homEquiv.symm y, by rw [← he, Equiv.apply_symm_apply]⟩
  have hloc : ∀ i, IsAffineHom (x.b ∣_ N.U i) ∧ LocallyOfFiniteType (x.b ∣_ N.U i) := by
    intro i
    obtain ⟨T, p, t, hpa, hpl, hex, hun⟩ := exists_torus_one (N.U i).toScheme
    have hb : ∀ k : Unit, ⊤ ≤ (p ≫ (N.U i).ι) ⁻¹ᵁ ((fun _ : Unit => N) k).U ((fun _ => i) k) :=
      fun k z _ => (p z).2
    let yT : Pt (fun _ : Unit => N) T :=
      Pt.ofChart (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t)
    obtain ⟨ψ, hψ⟩ := hsurj yT
    have hψb : ψ ≫ x.b = p ≫ (N.U i).ι := congrArg Pt.b hψ
    let ψ₀ : T ⟶ (x.b ⁻¹ᵁ N.U i).toScheme := IsOpenImmersion.lift (x.b ⁻¹ᵁ N.U i).ι ψ (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      change x.b (ψ z) ∈ N.U i
      rw [← Scheme.Hom.comp_apply, hψb, Scheme.Hom.comp_apply]
      exact (p z).2)
    have hψ₀ : ψ₀ ≫ (x.b ⁻¹ᵁ N.U i).ι = ψ := IsOpenImmersion.lift_fac _ _ _
    have hv : ⊤ ≤ (x.b ⁻¹ᵁ N.U i).ι ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => z.2
    obtain ⟨φ, hφp, hφt⟩ := hex _ (x.b ∣_ N.U i) (pb (x.b ⁻¹ᵁ N.U i).ι _ ⊤ hv (x.s () i))
    have h2 : ψ₀ ≫ φ = 𝟙 T := by
      refine hun T _ _ ?_ ?_
      · rw [Category.assoc, hφp, Category.id_comp, ← cancel_mono (N.U i).ι, Category.assoc,
          morphismRestrict_ι, ← Category.assoc, hψ₀, hψb]
      · have htop : ∀ {Y Z : Scheme.{0}} (f : Z ⟶ Y), ⊤ ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := fun f z _ => trivial
        have hφu : pb φ ⊤ ⊤ (htop φ) t = pb (x.b ⁻¹ᵁ N.U i).ι _ ⊤ hv (x.s () i) :=
          Units.ext ((pb_top _ _ _).trans hφt)
        have hψ' : ⊤ ≤ 𝟙 T ⁻¹ᵁ (ψ ≫ x.b) ⁻¹ᵁ N.U i := fun z _ => by
          have : (ψ ≫ x.b) z ∈ N.U i := by rw [hψb]; exact (p z).2
          exact this
        have hψ'' : ⊤ ≤ ψ ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => by
          have : (ψ ≫ x.b) z ∈ N.U i := by rw [hψb]; exact (p z).2
          exact this
        have e1 : pb (ψ₀ ≫ (x.b ⁻¹ᵁ N.U i).ι) (x.b ⁻¹ᵁ N.U i) ⊤ (hψ₀ ▸ hψ'') (x.s () i) =
            pb ψ (x.b ⁻¹ᵁ N.U i) ⊤ hψ'' (x.s () i) := pb_congr hψ₀ _ _ _ _
        have e2 : pb ψ (x.b ⁻¹ᵁ N.U i) ⊤ hψ'' (x.s () i) =
            pb (𝟙 T) _ ⊤ hψ' ((Pt.map ψ x).s () i) := (pb_id_comp ψ _ _ _ le_rfl hψ' _).symm
        have hbT : ⊤ ≤ 𝟙 T ⁻¹ᵁ (p ≫ (N.U i).ι) ⁻¹ᵁ N.U i := fun z _ => (p z).2
        have e3 : pb (𝟙 T) _ ⊤ hψ' ((Pt.map ψ x).s () i) = pb (𝟙 T) _ ⊤ hbT (yT.s () i) :=
          Pt.congr hψ () i (𝟙 T) ⊤ hψ' hbT
        have e4 : (pb (𝟙 T) _ ⊤ hbT (yT.s () i)).val = (Scheme.Hom.appTop (𝟙 T)).hom t.val :=
          Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t) () (𝟙 T) _
        refine (pb_top (ψ₀ ≫ φ) (htop _) t).symm.trans ?_
        rw [← pb_pb ψ₀ φ ⊤ ⊤ ⊤ (htop φ) (htop ψ₀), hφu, pb_pb]
        exact (congrArg Units.val (e1.trans (e2.trans e3))).trans e4
    have h1 : φ ≫ ψ₀ = 𝟙 _ := by
      rw [← cancel_mono (x.b ⁻¹ᵁ N.U i).ι, Category.assoc, hψ₀, Category.id_comp]
      refine hinj _ _ ?_
      have hbeq : (φ ≫ ψ) ≫ x.b = (x.b ⁻¹ᵁ N.U i).ι ≫ x.b := by
        rw [Category.assoc, hψb, ← Category.assoc, hφp, morphismRestrict_ι]
      have hx' : ⊤ ≤ φ ⁻¹ᵁ (ψ ≫ x.b) ⁻¹ᵁ N.U i := fun z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have hy' : ⊤ ≤ φ ⁻¹ᵁ (p ≫ (N.U i).ι) ⁻¹ᵁ N.U i := fun z _ => (p (φ z)).2
      have hA : ∀ k : Unit, ⊤ ≤ 𝟙 (x.b ⁻¹ᵁ N.U i).toScheme ⁻¹ᵁ ((φ ≫ ψ) ≫ x.b) ⁻¹ᵁ N.U i := fun _ z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have hB : ∀ k : Unit, ⊤ ≤ 𝟙 (x.b ⁻¹ᵁ N.U i).toScheme ⁻¹ᵁ ((x.b ⁻¹ᵁ N.U i).ι ≫ x.b) ⁻¹ᵁ N.U i := fun _ z _ => z.2
      have hC : ⊤ ≤ (φ ≫ ψ) ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have f1 : pb (𝟙 (x.b ⁻¹ᵁ N.U i).toScheme) _ ⊤ (hA ()) ((Pt.map (φ ≫ ψ) x).s () i) =
          pb (φ ≫ ψ) (x.b ⁻¹ᵁ N.U i) ⊤ hC (x.s () i) := pb_id_comp _ _ _ _ _ _ _
      have f2 : pb (𝟙 (x.b ⁻¹ᵁ N.U i).toScheme) _ ⊤ (hB ()) ((Pt.map (x.b ⁻¹ᵁ N.U i).ι x).s () i) =
          pb (x.b ⁻¹ᵁ N.U i).ι (x.b ⁻¹ᵁ N.U i) ⊤ hv (x.s () i) := pb_id_comp _ _ _ _ _ _ _
      have f3 : pb (φ ≫ ψ) (x.b ⁻¹ᵁ N.U i) ⊤ hC (x.s () i) =
          pb φ _ ⊤ hx' ((Pt.map ψ x).s () i) := (pb_pb φ ψ (x.b ⁻¹ᵁ N.U i) ((ψ ≫ x.b) ⁻¹ᵁ N.U i) ⊤ le_rfl hx' (x.s () i)).symm
      have f4 : pb φ _ ⊤ hx' ((Pt.map ψ x).s () i) = pb φ _ ⊤ hy' (yT.s () i) :=
        Pt.congr hψ () i φ ⊤ hx' hy'
      have f5 : (pb φ _ ⊤ hy' (yT.s () i)).val = φ.appTop.hom t.val :=
        Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t) () φ hy'
      refine Pt.ext_chart hbeq (fun _ => i) hA hB (fun k => ?_)
      cases k
      refine f1.trans (f3.trans (f4.trans (Units.ext ?_))) |>.trans f2.symm
      exact f5.trans hφt
    have : IsIso φ := ⟨⟨ψ₀, h1, h2⟩⟩
    rw [← hφp]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨G, x.b, fun i => (x.s () i)⁻¹, IsZariskiLocalAtTarget.of_iSup_eq_top N.U hN.cover
    fun i => (hloc i).1, IsZariskiLocalAtTarget.of_iSup_eq_top N.U hN.cover fun i => (hloc i).2,
    fun i i' => ?_, fun Z b s hs => ?_⟩
  · have hc : res (Scheme.Hom.preimage_mono x.b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (x.s () i') =
        pullU x.b _ (N.g i i') *
          res (Scheme.Hom.preimage_mono x.b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (x.s () i) := by
      rw [res_eq_pb, res_eq_pb, pullU_eq_pb]
      exact x.compat () i i' _ inf_le_left inf_le_right
    dsimp only
    rw [map_inv, map_inv, hc, mul_inv, mul_inv_cancel_left]
  · have hs' : ∀ i i' (W : Z.Opens) (h : W ≤ b ⁻¹ᵁ N.U i) (h' : W ≤ b ⁻¹ᵁ N.U i'),
        pb (𝟙 Z) (b ⁻¹ᵁ N.U i') W h' (s i')⁻¹ =
          pb b (N.U i ⊓ N.U i') W (le_inf h h') (N.g i i') * pb (𝟙 Z) (b ⁻¹ᵁ N.U i) W h (s i)⁻¹ := by
      intro i i' W h h'
      have := congrArg (pb (𝟙 Z) (b ⁻¹ᵁ (N.U i ⊓ N.U i')) W (le_inf h h')) (hs i i')
      rw [map_mul, res_eq_pb, res_eq_pb, pullU_eq_pb, pb_id_comp, pb_id_comp, pb_id_comp] at this
      rw [map_inv, map_inv, this, mul_inv, mul_inv_cancel_left]
    let y : Pt (fun _ : Unit => N) Z := ⟨b, fun _ i => (s i)⁻¹, fun _ i i' W h h' => hs' i i' W h h'⟩
    have key : ∀ g : Z ⟶ G, (∃ hg : g ≫ x.b = b, ∀ i, (g.appLE (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i)
        (by rw [← hg]; exact le_rfl)).hom ((x.s () i)⁻¹).val = (s i).val) ↔ Pt.map g x = y := by
      intro g
      constructor
      · rintro ⟨hg, h⟩
        refine (Pt.ext' (x := y) (y := Pt.map g x) hg.symm fun k i => ?_).symm
        cases k
        have h2 : (pb g _ (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i))⁻¹ = s i :=
          Units.ext ((pb_inv_val _ _ _ _ _).symm.trans (h i))
        have h3 : pb (𝟙 Z) ((g ≫ x.b) ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [hg]; exact le_rfl)
            (pb g (x.b ⁻¹ᵁ N.U i) ((g ≫ x.b) ⁻¹ᵁ N.U i) le_rfl (x.s () i)) =
              pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) :=
          pb_id_comp _ _ _ _ _ _ _
        exact (inv_eq_iff_eq_inv.1 h2).symm.trans h3.symm
      · intro h
        have hg : g ≫ x.b = b := congrArg Pt.b h
        refine ⟨hg, fun i => ?_⟩
        have := Pt.congr h () i (𝟙 Z) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) le_rfl
        have h3 : pb (𝟙 Z) ((g ≫ x.b) ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [hg]; exact le_rfl)
            (pb g (x.b ⁻¹ᵁ N.U i) ((g ≫ x.b) ⁻¹ᵁ N.U i) le_rfl (x.s () i)) =
              pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) :=
          pb_id_comp _ _ _ _ _ _ _
        have h4 : pb (𝟙 Z) (b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) le_rfl (s i)⁻¹ = (s i)⁻¹ := pb_id _ _
        have h5 : pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) =
            (s i)⁻¹ := h3.symm.trans (this.trans h4)
        rw [pb_inv_val, h5, inv_inv]
    obtain ⟨g0, hg0⟩ := hsurj y
    exact ⟨g0, (key g0).2 hg0, fun g hg => hinj _ _ (((key g).1 hg).trans hg0.symm)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphJetsMemPowSupUniformiser
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

theorem ker_productMap_le_span {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ']
    (ρ : κ →ₐ[ℂ] κ') :
    RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) ≤
      Ideal.span {x | ∃ f : κ, x = f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f} := by
  have key : ∀ x : κ ⊗[ℂ] κ',
      x - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x ∈
        Ideal.span {x | ∃ f : κ, x = f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f} := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      have e : f ⊗ₜ[ℂ] g - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') (f ⊗ₜ g) =
          (f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f) * (1 ⊗ₜ g) := by
        simp [Algebra.TensorProduct.productMap_apply_tmul, sub_mul,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨f, rfl⟩)
    | add x y hx hy =>
      have e : x + y - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') (x + y) =
          (x - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x) +
            (y - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') y) := by
        rw [map_add (f := _), TensorProduct.tmul_add]
        abel
      rw [e]
      exact add_mem hx hy
  intro x hx
  have h := key x
  rwa [RingHom.mem_ker.1 hx, TensorProduct.tmul_zero, sub_zero] at h


set_option maxHeartbeats 1000000 in
theorem jets_mem_pow_sup : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  graphIdeal E R π ρ ≤ 𝔭 → Irreducible t →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i →
    ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
    w ∈ 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} := by

  intro K κ κ' _ _ _ _ _ _ R π ρ E 𝔭 _ t hle ht hπC hC hfrac hR hord M l a b w hw hx
  let T := tens (κ' := κ') (placeAlg E)
  let I : Ideal T := 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩}
  let q : T →ₐ[ℂ] T ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hq0 : ∀ y : T, q y = 0 ↔ y ∈ I := fun y => by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  let jL : placeAlg E →ₐ[ℂ] T :=
    (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom.comp Algebra.TensorProduct.includeLeft
  let jR : κ' →ₐ[ℂ] T :=
    (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom.comp Algebra.TensorProduct.includeRight
  have hjL : ∀ e, (jL e : K ⊗[ℂ] κ') = (e : K) ⊗ₜ 1 := fun e => by
    simp [jL, tensMap]
  have hjR : ∀ c, (jR c : K ⊗[ℂ] κ') = 1 ⊗ₜ c := fun c => by
    simp [jR, tensMap]
  let ι : R →+* placeAlg E :=
    { toFun := fun r => ⟨r, hR _ r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hι : ∀ r : R, ((ι r : placeAlg E) : K) = r := fun _ => rfl

  have hg : ∀ r : R, jL (ι r) - jR (ρ (π r)) ∈ 𝔭 := fun r => by
    have e : ((jL (ι r) - jR (ρ (π r)) : T) : K ⊗[ℂ] κ') = (r : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π r) := by
      rw [Subalgebra.coe_sub, hjL (ι r), hjR (ρ (π r))]
      rfl
    exact hle (Ideal.subset_span (Or.inr ⟨r, e⟩))

  have hk : ∀ r : R, π r = 0 → q (jL (ι r)) = 0 := by
    intro r hr
    rw [hq0]
    apply Ideal.mem_sup_right
    by_cases h0 : (r : K) = 0
    · have e : jL (ι r) = 0 := Subtype.ext (by simp [hjL, hι, h0])
      rw [e]
      exact zero_mem _
    have hpos := (hord r h0).1 hr
    have hnu : ¬ IsUnit (⟨r, hR _ r.2⟩ : E.ring) := fun hu => by
      have h1 := E.ord_eq_zero hu
      simp only at h1
      omega
    have hm : (⟨r, hR _ r.2⟩ : E.ring) ∈ Ideal.span {t} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht]
      exact hnu
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hm
    rw [Ideal.mem_span_singleton']
    refine ⟨jL ⟨u, u.2⟩, Subtype.ext ?_⟩
    have hu' : (u : K) * t = r := congrArg Subtype.val hu
    simp only [Subalgebra.coe_mul, hjL, hι, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hu']

  have hu : ∀ r : R, π r ≠ 0 → IsUnit (q (jL (ι r))) := by
    intro r hr
    have hρ : IsUnit (q (jR (ρ (π r)))) :=
      ((isUnit_iff_ne_zero.2 ((map_ne_zero ρ).2 hr)).map jR).map q
    have hn : IsNilpotent (q (jL (ι r) - jR (ρ (π r)))) :=
      ⟨M, by rw [← map_pow, hq0]; exact Ideal.mem_sup_left (Ideal.pow_mem_pow (hg r) M)⟩
    have h := IsNilpotent.isUnit_add_left_of_commute hn hρ (Commute.all _ _)
    rwa [map_sub, add_sub_cancel] at h

  let φ : R →+* T ⧸ I := (q : T →+* T ⧸ I).comp ((jL : placeAlg E →+* T).comp ι)
  have hφ : ∀ r, φ r = q (jL (ι r)) := fun _ => rfl
  have hker : RingHom.ker π.rangeRestrict ≤ RingHom.ker φ := fun r hr => by
    rw [RingHom.mem_ker] at hr ⊢
    exact hk r (congrArg Subtype.val hr)
  let ψ : π.range →+* T ⧸ I :=
    π.rangeRestrict.liftOfRightInverse (Function.surjInv π.rangeRestrict_surjective)
      (Function.rightInverse_surjInv _) ⟨φ, hker⟩
  have hψ : ∀ r, ψ (π.rangeRestrict r) = q (jL (ι r)) := fun r =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ r
  haveI : IsFractionRing π.range κ := by
    refine ⟨fun y => ?_, fun z => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    · refine isUnit_iff_ne_zero.2 fun h => nonZeroDivisors.coe_ne_zero y (Subtype.ext h)
    · obtain ⟨c, d, hd, e⟩ := hfrac z
      exact ⟨(π.rangeRestrict c, ⟨π.rangeRestrict d, mem_nonZeroDivisors_of_ne_zero
        fun h => hd (congrArg Subtype.val h)⟩), e⟩
  have hunit : ∀ y : nonZeroDivisors π.range, IsUnit (ψ y) := by
    rintro ⟨⟨v, d, rfl⟩, hy⟩
    have hd : π d ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero ⟨_, hy⟩ (Subtype.ext h)
    exact (hψ d).symm ▸ hu d hd
  let θ₀ : κ →+* T ⧸ I := IsLocalization.lift (M := nonZeroDivisors π.range) hunit
  have hθ₀ : ∀ r, θ₀ (π r) = q (jL (ι r)) := fun r =>
    (IsLocalization.lift_eq (M := nonZeroDivisors π.range) hunit (π.rangeRestrict r)).trans (hψ r)

  let θ₀A : κ →ₐ[ℂ] T ⧸ I :=
    { θ₀ with
      commutes' := fun c => by
        have e1 : algebraMap ℂ κ c = π ⟨algebraMap ℂ K c, hC c⟩ := (hπC c (hC c)).symm
        have e2 : ι ⟨algebraMap ℂ K c, hC c⟩ = algebraMap ℂ (placeAlg E) c := Subtype.ext rfl
        change θ₀ (algebraMap ℂ κ c) = _
        rw [e1, hθ₀, e2, AlgHom.commutes, AlgHom.commutes] }
  let θ : κ ⊗[ℂ] κ' →ₐ[ℂ] T ⧸ I := Algebra.TensorProduct.productMap θ₀A (q.comp jR)
  have hθt : ∀ f c, θ (f ⊗ₜ c) = θ₀ f * q (jR c) := fun f c =>
    Algebra.TensorProduct.productMap_apply_tmul _ _ _ _

  have hwx : θ (∑ i, π (a i) ⊗ₜ[ℂ] b i) = q w := by
    have ew : w = ∑ i, jL (ι (a i)) * jR (b i) := by
      apply Subtype.ext
      rw [hw]
      simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, hjL, hjR, hι,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ew, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hθt, hθ₀, map_mul]

  have hgen : Ideal.map θ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ≤
      Ideal.map q 𝔭 := by
    refine (Ideal.map_mono (ker_productMap_le_span ρ)).trans ?_
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
    obtain ⟨c, d, hd, e⟩ := hfrac f
    have hfd : θ₀ f * q (jL (ι d)) = q (jL (ι c)) := by rw [← hθ₀, ← hθ₀, ← map_mul, e]
    set u := θ (f ⊗ₜ 1 - 1 ⊗ₜ ρ f) with hu_def
    have hu1 : u = θ₀ f - q (jR (ρ f)) := by
      rw [hu_def, map_sub, hθt, hθt]
      simp only [map_one, mul_one, one_mul]
    have h2 : u * q (jL (ι d)) =
        q (jL (ι c) - jR (ρ (π c))) - q (jR (ρ f)) * q (jL (ι d) - jR (ρ (π d))) := by
      rw [hu1, sub_mul, hfd, ← e, map_mul ρ, map_mul jR, map_sub q (jL (ι c)), map_sub q (jL (ι d)),
        map_mul q]
      rw [mul_sub, sub_sub_sub_cancel_right]
    have h3 : u * q (jL (ι d)) ∈ Ideal.map q 𝔭 := by
      rw [h2]
      exact sub_mem (Ideal.mem_map_of_mem q (hg c))
        (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem q (hg d)))
    obtain ⟨v, hv⟩ := (hu d hd).exists_right_inv
    have h4 : u = u * q (jL (ι d)) * v := by rw [mul_assoc, hv, mul_one]
    rw [SetLike.mem_coe, h4]
    exact Ideal.mul_mem_right _ _ h3
  have hbot : Ideal.map q 𝔭 ^ M = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro y hy
    rw [RingHom.mem_ker]
    exact (hq0 y).2 (Ideal.mem_sup_left hy)
  have h1 := Ideal.mem_map_of_mem θ hx
  rw [Ideal.map_pow] at h1
  have h2 := Ideal.pow_right_mono hgen M h1
  rw [hbot, Ideal.mem_bot] at h2
  exact (hq0 w).1 (hwx.symm.trans h2)

end GlobalTheory.GraphLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem sig_X'_eq_sig_Y (D : D7) (τ : D.host.E →+* ℂ) : D.sp.X'.sig τ = (D.sp.Y D.R.m).sig τ := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have hw : (Matrix.of fun i j => (D.sp.Y D.R.m).hT (D.sp.eYm (D.sp.X'.frame i)) (D.sp.eYm (D.sp.X'.frame j))) =
      D.sp.X'.gram := by
    exact Matrix.ext fun i j => D.sp.eYm_isom _ _
  have hs := D.sp.X'_sig τ
  rw [← hw] at hs
  have k := sig_family (D.sp.Y D.R.m) τ hτ _ hs (D.sp.Y_sig D.R.m τ)
  have h3 := sig_sum _ D.sp.X'_sig τ
  have h4 := sig_sum _ (D.sp.Y_sig D.R.m) τ
  have hYr : (D.sp.Y D.R.m).rank = D.sp.X'.rank := by
    rw [D.sp.Y_rank D.R.m le_rfl, D.sp.X'_rank]; rfl
  rw [hYr] at k h4
  exact Prod.ext (by omega) (by omega)

theorem colY_isV : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ j, j ≤ D.R.m → (columnBlock L j).IsV (rankV D 0 j) ((D.R.m - j) / 2) := by
  intro D T L μ0 hL j hj
  have hr : rankV D 0 j = D.R.rankY j := by
    simp only [rankV, zero_mul, add_zero]; rfl
  rw [hr]
  rcases hj.eq_or_lt with rfl | hlt
  · rw [colY_m]
    refine ⟨D.sp.X'_rank, D.sp.X'_sig, fun τ => ?_,
      GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX⟩
    exact (sig_X'_eq_sig_Y D τ).trans (D.Y_sigval _ le_rfl τ)
  · rw [colY_lt L hlt]
    have e : min j D.R.m = j := min_eq_left hj
    refine ⟨?_, D.sp.Y_sig _, fun τ => ?_,
      GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY j hlt)⟩
    · exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [e])
    · exact (D.Y_sigval _ (min_le_right _ _) τ).trans (by rw [e]; rfl)

end GlobalTheory.ChiGrid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeNonnegOfSemiPos
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

noncomputable section

namespace GlobalTheory.HSNef

open MeasureTheory

theorem gdeg_nonneg_of_semiPos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ L : HermLB p, L.SemiPos D → 0 ≤ gdeg L D := by
  intro k _ X _ p D _ L hL
  unfold gdeg chInt
  refine finsum_nonneg fun σ => ?_
  rw [Weight.chernInt, Weight.chernPart_neg_eq_zero (L.cInf σ) (hL σ)]
  simp only [Measure.restrict_zero, integral_zero_measure, sub_zero]
  exact integral_nonneg fun _ => zero_le_one

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOffCoordinateHyperplanesStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_offCoordinateHyperplanes : ∀ {n : ℕ} (S : Finset (Fin n)) (U : Set (V n)), IsOpen U → IsOpen (offHyp S U) := by
  first | exact @GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen | exact GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen | (intros; apply GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen <;> assumption)
end

