module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2598
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2399
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionDescendsFromAlgClosedField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningMorphismsAgreeBeyondThreshold
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_closedFibre_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (e : ℕ) (K : Type) [Field K] (a : Spec (CommRingCat.of K) ⟶ (thickObj R (maximalIdeal R) e G).left), ∃ g : Spec (CommRingCat.of K) ⟶ (thickObj R (maximalIdeal R) 0 G).left, g ≫ (fstG (maximalIdeal R) 0 G).left = a ≫ (fstG (maximalIdeal R) e G).left ∧ g ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = a ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e := by
  intro R _ _ _ G e K _ a
  let f := a ≫ (thickObj R (maximalIdeal R) e G).hom
  let φ := Spec.preimage f
  have hφ : Spec.map φ = f := Spec.map_preimage f
  have hker : ∀ r ∈ maximalIdeal R ^ (0 + 1),
      (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) r = 0 := by
    intro r hr
    rw [zero_add, pow_one] at hr
    have h1 : r ^ (e + 1) ∈ maximalIdeal R ^ (e + 1) := Ideal.pow_mem_pow hr _
    have h2 : (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) r ^ (e + 1) = 0 := by
      rw [← map_pow, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 h1, map_zero]
    exact pow_eq_zero_iff (Nat.succ_ne_zero e) |>.1 h2
  let ψ : R ⧸ maximalIdeal R ^ (0 + 1) →+* K := Ideal.Quotient.lift _ _ hker
  have hψ : (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))) ≫ CommRingCat.ofHom ψ =
      CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) ≫ φ := by
    ext r
    exact Ideal.Quotient.lift_mk (maximalIdeal R ^ (0 + 1)) (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) hker
  have hc : (a ≫ pullback.fst G.hom (thick R (maximalIdeal R) e)) ≫ G.hom =
      Spec.map (CommRingCat.ofHom ψ) ≫ thick R (maximalIdeal R) 0 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change f ≫ _ = _
    rw [← hφ, thick, thick, ← Spec.map_comp, ← Spec.map_comp, hψ]
  refine ⟨pullback.lift _ _ hc, pullback.lift_fst _ _ _, ?_⟩
  change pullback.lift _ _ hc ≫ pullback.snd _ _ ≫ _ = a ≫ pullback.snd _ _ ≫ _
  rw [pullback.lift_snd_assoc, ← hc, Category.assoc, pullback.condition]

theorem eq_of_germRatioAgree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (Z : Scheme.{0}) (u u' : Z ⟶ (thickObj R (maximalIdeal R) e G).left), u ≫ (thickObj R (maximalIdeal R) e G).hom = u' ≫ (thickObj R (maximalIdeal R) e G).hom → ∀ (s₀ : H0 U.LG.L k) (i i'' : Fin 1 → U.LG.L.ι) (z : Z), GermRatioAgree (u ≫ (fstG (maximalIdeal R) e G).left) (u' ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' z → u z = u' z := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨Y⟩ : Nonempty (Ext D.toPre) := inferInstance
  obtain ⟨S, k₁, hk₁⟩ := _root_.GlobalTheory.Mum.ThetaImm.exists_immersion R hB D Y
  choose k₀f hk₀f using (_root_.GlobalTheory.ThFam.exists_intFam_lead R hB D).1
  refine ⟨max 3 (max k₁ (S.sup k₀f)), le_max_left _ _, ?_⟩
  intro e k hk Z u u' hu s₀ i i'' z h
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hkk₁ : k₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkS : S.sup k₀f ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨N, α, b, τ, hτ, hαb, himm⟩ := hk₁ k hkk₁
  have hF : ∀ j, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead (α j) (b j) := fun j =>
    hk₀f (α j) k (le_trans (Finset.le_sup (hαb j).1) hkS) (b j)
  choose F hF using hF
  have hs : ∀ j, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ (F j).f := fun j =>
    IntFam.exists_expandsAt R hB D A G U hG k (by omega) (F j)
  choose s hs using hs
  obtain ⟨hzi, hzi'', hu0, hu0', hrat⟩ := h
  set p := (fstG (maximalIdeal R) e G).left with hp
  have minor : ∀ j l, secGerm (u ≫ p) z (s j) i * secGerm (u' ≫ p) z (s l) i'' =
      secGerm (u ≫ p) z (s l) i * secGerm (u' ≫ p) z (s j) i'' := by
    intro j l
    have h1 := hrat (s j)
    have h2 := hrat (s l)
    apply (hu0.mul hu0').mul_left_cancel
    linear_combination (secGerm (u ≫ p) z s₀ i * secGerm (u' ≫ p) z (s l) i'') * h1 -
      (secGerm (u ≫ p) z s₀ i * secGerm (u' ≫ p) z (s j) i'') * h2

  let K := Z.residueField z
  let x : Spec (CommRingCat.of K) ⟶ Z := Z.fromSpecResidueField z
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  have hx : x pt = z := Scheme.fromSpecResidueField_apply z pt
  have minorx : ∀ j l, secGerm (x ≫ u ≫ p) pt (s j) i * secGerm (x ≫ u' ≫ p) pt (s l) i'' =
      secGerm (x ≫ u ≫ p) pt (s l) i * secGerm (x ≫ u' ≫ p) pt (s j) i'' := by
    intro j l
    have hi : (u ≫ p) (x pt) ∈ secChart U.LG.L i := hx ▸ hzi
    have hi'' : (u' ≫ p) (x pt) ∈ secChart U.LG.L i'' := hx ▸ hzi''
    have m := hx ▸ minor j l
    rw [secGerm_comp x (u ≫ p) pt _ hi, secGerm_comp x (u ≫ p) pt _ hi, secGerm_comp x (u' ≫ p) pt _ hi'',
      secGerm_comp x (u' ≫ p) pt _ hi'', ← map_mul, ← map_mul, m]

  obtain ⟨g, hg1, hg2⟩ := exists_closedFibre_factor R G e K (x ≫ u)
  obtain ⟨g', hg1', hg2'⟩ := exists_closedFibre_factor R G e K (x ≫ u')
  let T : Over (Sp R) := Over.mk ((x ≫ u) ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e)
  have hgT : g ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = T.hom := hg2
  have hgT' : g' ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = T.hom := by
    rw [hg2']; show _ = (x ≫ u) ≫ _
    simp only [Category.assoc, ← reassoc_of% hu]
  obtain ⟨ξ, hξ⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) g hgT
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) g' hgT'
  set y := (Y.Φ T).symm ξ with hy
  set y' := (Y.Φ T).symm ξ' with hy'
  have hyξ : Y.Φ T y = ξ := Equiv.apply_symm_apply _ _
  have hyξ' : Y.Φ T y' = ξ' := Equiv.apply_symm_apply _ _
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusCoord.exists_good' U.LG.isLB pt
  obtain ⟨J', hJ'⟩ := GlobalTheory.TorusCoord.exists_good' D.toPre.P.isLB pt
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term R D A G U.toUnifPre Y T g y (hyξ ▸ hξ) k pt J J' hJ hJ'
  obtain ⟨c', hc'⟩ := _root_.GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term R D A G U.toUnifPre Y T g' y' (hyξ' ▸ hξ') k pt J J' hJ hJ'
  have hv : ∀ j, secGerm (x ≫ u ≫ p) pt (s j) (fun _ => J ((x ≫ u ≫ p) ≫ 𝟙 _)) = c.val * sval (τ j) y.left pt J' := by
    intro j
    have := hc (α j) (b j) (τ j) (F j) (s j) (hαb j).2 (hF j) (hs j 0)
    rw [hg1, Category.assoc] at this
    exact this
  have hv' : ∀ j, secGerm (x ≫ u' ≫ p) pt (s j) (fun _ => J ((x ≫ u' ≫ p) ≫ 𝟙 _)) = c'.val * sval (τ j) y'.left pt J' := by
    intro j
    have := hc' (α j) (b j) (τ j) (F j) (s j) (hαb j).2 (hF j) (hs j 0)
    rw [hg1', Category.assoc] at this
    exact this
  have hi : (x ≫ u ≫ p) pt ∈ secChart U.LG.L i := by
    rw [Scheme.Hom.comp_apply, hx]; exact hzi
  have hi'' : (x ≫ u' ≫ p) pt ∈ secChart U.LG.L i'' := by
    rw [Scheme.Hom.comp_apply, hx]; exact hzi''
  obtain ⟨a, ha⟩ := exists_unit_secGerm k (x ≫ u ≫ p) pt hi (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (x ≫ u ≫ p))
  obtain ⟨a', ha'⟩ := exists_unit_secGerm k (x ≫ u' ≫ p) pt hi'' (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (x ≫ u' ≫ p))
  have minorτ : ∀ j l, sval (τ j) y.left pt J' * sval (τ l) y'.left pt J' = sval (τ l) y.left pt J' * sval (τ j) y'.left pt J' := by
    intro j l
    have m := minorx j l
    rw [ha, ha, ha', ha', hv, hv, hv', hv'] at m
    apply (((a.isUnit.mul a'.isUnit).mul c.isUnit).mul c'.isUnit).mul_left_cancel
    linear_combination m
  obtain ⟨W, hW, hWy⟩ := _root_.GlobalTheory.Mum.ThetaSep.agree_near_of_minors R D.toPre Y k N τ hτ himm T y y' pt J' hJ' minorτ
  have hWt : W = ⊤ := by
    exact eq_top_iff.2 fun q _ => (Subsingleton.elim (α := Spec (CommRingCat.of K)) q pt) ▸ hW
  subst hWt
  have : IsIso (⊤ : (T.left).Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  have hyy : y = y' := Over.OverMorphism.ext ((cancel_epi _).1 hWy)
  have hξξ : ξ = ξ' := by rw [← hyξ, ← hyξ', hyy]
  have hgg : g = g' := GlobalTheory.TorusCoord.IsPointOf.unique_left (U.gt 0) hξ (hξξ ▸ hξ')
  have hpp : (x ≫ u ≫ p) pt = (x ≫ u' ≫ p) pt := by
    rw [← Category.assoc, ← hg1, ← Category.assoc, ← hg1', hgg]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx] at hpp
  have : IsClosedImmersion p := by
    show IsClosedImmersion (pullback.fst G.hom (thick R (maximalIdeal R) e))
    have : IsClosedImmersion (thick R (maximalIdeal R) e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  exact p.isClosedEmbedding.injective hpp

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimLeZeroFibreAffineOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem dim_le_zero_of_fib_of_subset_affine : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), GlobalTheory.MixHt.IsAmb p → ∀ (ℓ : ℕ) (U : X.Opens) (C : Set X), ℓ.Prime → IsAffineOpen U → IsIrreducible C → IsClosed C → C ⊆ GlobalTheory.HSAmp.fib X ℓ → C ⊆ (U : Set X) → topologicalKrullDim C ≤ 0 := by
  intro k _ X p h ℓ U C hℓ hU hC hCc hfib hCU
  obtain ⟨η, hη⟩ := QuasiSober.sober hC hCc
  set Y := GlobalTheory.MixHt.clo η
  set i := GlobalTheory.MixHt.cloι η
  have hgen : i (genericPoint Y) = η := GlobalTheory.MixHt.cloι_genericPoint η
  have hrange : i '' Set.univ = C := by
    rw [← (genericPoint_spec Y).def, ← i.isClosedEmbedding.closure_image_eq, Set.image_singleton, hgen, hη.def]
  have htop : i ⁻¹ᵁ U = ⊤ := by
    refine top_unique fun y _ => ?_
    exact hCU (hrange ▸ Set.mem_image_of_mem i (Set.mem_univ y))
  have hV : IsAffineOpen (⊤ : Y.Opens) := htop ▸ hU.preimage i
  have hA := h.sub i
  have := hA.finite
  have : IsProper (i ≫ p) := by
    obtain ⟨N, j, _, hj⟩ := hA.isProjOver
    have := isProper_str k N
    exact hj ▸ inferInstance

  have hφ := isIntegral_appTop_of_universallyClosed (i ≫ p)
  let A := Γ(Sp k, ⊤)
  let R := Γ(Y, ⊤)
  let e : A ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hAint : Algebra.IsIntegral ℤ A :=
    Algebra.IsIntegral.of_surjective e.symm.toRingHom.toIntAlgHom e.symm.surjective
  letI : Algebra A R := (i ≫ p).appTop.hom.toAlgebra
  have hRA : Algebra.IsIntegral A R := ⟨hφ⟩
  have hRint : Algebra.IsIntegral ℤ R := Algebra.IsIntegral.trans A

  have hchar : ((ℓ : ℕ) : R) = 0 := by
    have hcX : CharP (X.residueField η) ℓ := ringChar.eq_iff.mp (hfib hη.mem)
    have h1 : ((ℓ : ℕ) : X.residueField (i (genericPoint Y))) = 0 := by
      rw [hgen]; exact CharP.cast_eq_zero _ ℓ
    have h2 : ((ℓ : ℕ) : Y.residueField (genericPoint Y)) = 0 := by
      have := congrArg (i.residueFieldMap (genericPoint Y)).hom h1
      simpa using this
    have hinj : Function.Injective ((Y.residue (genericPoint Y)).hom.comp
        (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom) :=
      (RingHom.injective (Y.residue (genericPoint Y)).hom).comp
        (germ_injective_of_isIntegral Y (U := ⊤) (genericPoint Y) trivial)
    apply hinj
    simpa using h2

  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP R ℓ := (CharP.charP_iff_prime_eq_zero hℓ).2 hchar
  letI : Algebra (ZMod ℓ) R := ZMod.algebra R ℓ
  have : Algebra.IsIntegral (ZMod ℓ) R := Algebra.IsIntegral.tower_top ℤ
  have hR : IsField R := isField_of_isIntegral_of_isField' (Field.toIsField (ZMod ℓ))

  have hdimY : topologicalKrullDim ((⊤ : Y.Opens) : Set Y) = 0 := by
    rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding hV.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := R)).trans (ringKrullDim_eq_zero_of_isField hR)
  rw [← hrange, GlobalTheory.MixHt.DimBasic.dim_image i.isClosedEmbedding.isEmbedding]
  rw [TopologicalSpace.Opens.coe_top] at hdimY
  exact hdimY.le

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionPointCharacterEqWeilPairingLabelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricTorsionPoint_character_eq_weilPairing_label : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (c : 𝔪.D.toPre.X →+ ℤ) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), TorAt 𝔪.U (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))))) c x → x.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt τ).left → ∀ a mu, 𝔪.YY a mu → ((c (𝔪.e₈ mu) : ℤ) : ZMod (X₁.S.r * X₁.S.N)) = ((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.torAt_char_eq_weil | exact GlobalTheory.Poinc.Sep.Spz.torAt_char_eq_weil | (intros; apply GlobalTheory.Poinc.Sep.Spz.torAt_char_eq_weil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionPointOfTorusPointAtClosedPointFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricTorsionPoint_of_torusPoint_at_closedPointField : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (β : G.left ⟶ H.left), IsGrpPullback G H ξ β → ∀ (σ : Sp V ⟶ H.left), σ ≫ H.hom = ξ → ∀ (k : ℕ) (w : V), 1 ≤ k → IsUnit (k : V) → w ^ k = 1 → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (c : D.toPre.X →+ ℤ) (x : TFK (R := V) F ⟶ A.A), x ^ k = 1 → x.left ≫ genMap U ≫ β = spMap (algebraMap (FractionRing V) F) ≫ jK V ≫ σ → ∀ (κ : Type) [Field κ] (b : V →+* κ) (hb : ∀ y ∈ maximalIdeal V ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G.left) (hm : IsGrpPullback Gκ G (spMap b) m) (τ : Multiplicative D.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b w ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ σ = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb hm).left ≫ m ≫ β → TorAt U F k (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) c x := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.torAt_of_closedPoint | exact GlobalTheory.Poinc.Sep.Spz.torAt_of_closedPoint | (intros; apply GlobalTheory.Poinc.Sep.Spz.torAt_of_closedPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionSectionEqTorusPointAtClosedPointFielStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricTorsionSection_eq_torusPoint_at_closedPointField : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (β : G.left ⟶ H.left), IsGrpPullback G H ξ β → ∀ (σ : Sp V ⟶ H.left), σ ≫ H.hom = ξ → ∀ (k : ℕ) (w : V), 1 ≤ k → w ^ k = 1 → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (c : D.toPre.X →+ ℤ) (x : TFK (R := V) F ⟶ A.A), TorAt U F k (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) c x → x.left ≫ genMap U ≫ β = spMap (algebraMap (FractionRing V) F) ≫ jK V ≫ σ → ∀ (κ : Type) [Field κ] (b : V →+* κ) (hb : ∀ y ∈ maximalIdeal V ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G.left) (hm : IsGrpPullback Gκ G (spMap b) m) (τ : Multiplicative D.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b w ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ σ = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb hm).left ≫ m ≫ β := by
  first | exact @GlobalTheory.ToricTorsionClosedPt.main | exact GlobalTheory.ToricTorsionClosedPt.main | (intros; apply GlobalTheory.ToricTorsionClosedPt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsConstantCompletedLocalRingClosedPoi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.LabConst

theorem mk_eq_of_forall_char {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ) (β₁ β₂ : X)
    (h : ∀ lam : X →+ ZMod k, lam β₁ = lam β₂) :
    (QuotientAddGroup.mk β₁ : X ⧸ (nsmulAddMonoidHom k : X →+ X).range) = QuotientAddGroup.mk β₂ := by
  let b := Module.Free.chooseBasis ℤ X
  rw [QuotientAddGroup.eq]
  have hc : ∀ i, (k : ℤ) ∣ b.repr (-β₁ + β₂) i := by
    intro i
    have h1 := h ((Int.castAddHom (ZMod k)).comp (b.coord i).toAddMonoidHom)
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply, Int.coe_castAddHom] at h1
    simp only [map_add (f := _), map_neg, Finsupp.add_apply, Finsupp.neg_apply, Int.cast_add, Int.cast_neg, h1, neg_add_cancel]
  choose c hc using hc
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [nsmulAddMonoidHom_apply]
  conv_rhs => rw [← b.sum_repr (-β₁ + β₂)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i, mul_smul, natCast_zsmul]

def qmap {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) :
    X ⧸ (nsmulAddMonoidHom k : X →+ X).range →+ Y ⧸ (nsmulAddMonoidHom k : Y →+ Y).range :=
  QuotientAddGroup.map _ _ e.toAddMonoidHom (by
    rintro _ ⟨z, rfl⟩
    exact ⟨e z, by simp⟩)

theorem qmap_mk {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) (β : X) :
    qmap k e (QuotientAddGroup.mk β) = QuotientAddGroup.mk (e β) := rfl

theorem mk_symm_eq_iff {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) (β : Y) (α : X) :
    (QuotientAddGroup.mk (e.symm β) : X ⧸ (nsmulAddMonoidHom k : X →+ X).range) = QuotientAddGroup.mk α ↔
      (QuotientAddGroup.mk β : Y ⧸ (nsmulAddMonoidHom k : Y →+ Y).range) = QuotientAddGroup.mk (e α) := by
  rw [QuotientAddGroup.eq, QuotientAddGroup.eq]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨e z, ?_⟩
    rw [nsmulAddMonoidHom_apply] at hz ⊢
    rw [← map_nsmul, hz, map_add (f := _), map_neg, AddEquiv.apply_symm_apply]
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, ?_⟩
    rw [nsmulAddMonoidHom_apply] at hz ⊢
    rw [← map_nsmul, hz, map_add (f := _), map_neg, AddEquiv.symm_apply_apply]

end GlobalTheory.Poinc.LabConst

namespace GlobalTheory.Poinc.LabConst

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∃ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (l : u.Lab) a α, yy a = QuotientAddGroup.mk α ↔ l.yy a = QuotientAddGroup.mk (ε α) := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi
  obtain ⟨sg, hread⟩ := GlobalTheory.T.torsionLabel_eq_weilPairing_toricTorsionPoint o' Ω S ρ
  have hglob := GlobalTheory.T.exists_toricTorsion_label_closed_point o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
  choose bOf hbOf using hglob
  have hk0 : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  have hζk : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (by positivity) (by ring)
  have key : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y →
      spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ →
      ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε →
      ∀ (l : u.Lab) (a : S.Gam) (β : u.D.toPre.X), l.yy a = QuotientAddGroup.mk β →
      ∀ lam : D.toPre.X →+ ZMod (S.r * S.N), lam (ε.symm β) = ((sg : ℤ) • eStd S.g _ (bOf lam) a) := by
    intro p _ y ev hCen hev y₀ hAt u ε hbc l a β hβ lam
    haveI : IsDomain o' := (ArithBase.ded (o := o') (Ω := Ω)).toIsDomain
    set f : o' →+* PadicAlgCl p := y₀.comp (algebraMap o' S.R) with hf
    have hω : IsPrimitiveRoot (f (S.ζ ^ (S.r * S.N))) (S.r * S.N) := by
      have h1 := hζk.isRoot_cyclotomic hk0
      have h2 := h1.map (f := f)
      rw [Polynomial.map_cyclotomic] at h2
      exact (Polynomial.isRoot_cyclotomic_iff_charZero hk0).1 h2
    set ω : (PadicAlgCl p)ˣ := (hω.isUnit hk0.ne').unit with hωdef
    have hωk : ω ^ (S.r * S.N) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hωdef, IsUnit.unit_spec, hω.pow_eq_one, Units.val_one])
    let ψ : ZMod (S.r * S.N) →+ Additive (PadicAlgCl p)ˣ :=
      ZMod.lift (S.r * S.N) ⟨zmultiplesHom (Additive (PadicAlgCl p)ˣ) (Additive.ofMul ω), by
        rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hωk, ofMul_one]⟩
    have hψ : ∀ z : ZMod (S.r * S.N), ((Additive.toMul (ψ z) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = f (S.ζ ^ (S.r * S.N)) ^ z.val := by
      intro z
      haveI : NeZero (S.r * S.N) := NeZero.of_pos hk0
      conv_lhs => rw [← ZMod.intCast_zmod_cast z]
      rw [ZMod.lift_coe]
      simp only [Subtype.coe_mk, zmultiplesHom_apply, toMul_zsmul, toMul_ofMul, ZMod.cast_eq_val, zpow_natCast]
      rw [Units.val_pow_eq_pow_val, hωdef, IsUnit.unit_spec]
    let τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ :=
      AddMonoidHom.toMultiplicativeLeft (ψ.comp (lam.comp ε.symm.toAddMonoidHom))
    have hτ : ∀ χ' : u.D.toPre.X, ((τ' (Multiplicative.ofAdd χ') : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
        f (S.ζ ^ (S.r * S.N)) ^ (lam (ε.symm χ')).val := fun χ' => hψ _
    have hτk : τ' ^ (S.r * S.N) = 1 := by
      refine MonoidHom.ext fun χ' => Units.ext ?_
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply, Units.val_one]
      obtain ⟨χ, rfl⟩ : ∃ χ, Multiplicative.ofAdd χ = χ' := ⟨Multiplicative.toAdd χ', rfl⟩
      rw [hτ, ← pow_mul, Nat.mul_comm _ (S.r * S.N), pow_mul, hω.pow_eq_one, one_pow]
    have hglobτ : ∀ χ, ((τ' (Multiplicative.ofAdd (ε χ)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
        y₀ (algebraMap o' S.R S.ζ) ^ (S.r * S.N * (lam χ).val) := by
      intro χ
      rw [hτ, AddEquiv.symm_apply_apply]
      simp only [hf, RingHom.comp_apply, map_pow, pow_mul]
    have hpt := hbOf lam p y ev hCen hev y₀ hAt u ε hbc τ' hglobτ
    have hv := hread p y₀ u l τ' (bOf lam) hτk hpt a β hβ
    have hv' : f (S.ζ ^ (S.r * S.N)) ^ (lam (ε.symm β)).val =
        f (S.ζ ^ (S.r * S.N)) ^ (((sg : ℤ) • eStd S.g _ (bOf lam) a).val) := by
      rw [← hτ, hv]
      simp only [hf, RingHom.comp_apply, map_pow, pow_mul]
    exact ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hv')
  have hconst : ∀ (p₁ : ℕ) [Fact p₁.Prime] (y₁ : Sp (OO p₁) ⟶ M.Z) (ev₁ : R →+* OO p₁), M.Cen U₀ x y₁ →
      spMap ev₁ ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y₁ → ∀ y₀₁ : S.R →+* PadicAlgCl p₁, S.At M y₁ y₀₁ →
      ∀ (u₁ : ρ.UTest p₁ y₀₁) (ε₁ : D.toPre.X ≃+ u₁.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev₁ u₁ ε₁ →
      ∀ (l₁ : u₁.Lab) (p₂ : ℕ) [Fact p₂.Prime] (y₂ : Sp (OO p₂) ⟶ M.Z) (ev₂ : R →+* OO p₂), M.Cen U₀ x y₂ →
      spMap ev₂ ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y₂ → ∀ y₀₂ : S.R →+* PadicAlgCl p₂, S.At M y₂ y₀₂ →
      ∀ (u₂ : ρ.UTest p₂ y₀₂) (ε₂ : D.toPre.X ≃+ u₂.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev₂ u₂ ε₂ →
      ∀ (l₂ : u₂.Lab) (a : S.Gam), qmap (S.r * S.N) ε₁.symm (l₁.yy a) = qmap (S.r * S.N) ε₂.symm (l₂.yy a) := by
    intro p₁ _ y₁ ev₁ hCen₁ hev₁ y₀₁ hAt₁ u₁ ε₁ hbc₁ l₁ p₂ _ y₂ ev₂ hCen₂ hev₂ y₀₂ hAt₂ u₂ ε₂ hbc₂ l₂ a
    obtain ⟨β₁, hβ₁⟩ := QuotientAddGroup.mk_surjective (l₁.yy a)
    obtain ⟨β₂, hβ₂⟩ := QuotientAddGroup.mk_surjective (l₂.yy a)
    rw [← hβ₁, ← hβ₂, qmap_mk, qmap_mk]
    refine mk_eq_of_forall_char _ _ _ fun lam => ?_
    rw [key p₁ y₁ ev₁ hCen₁ hev₁ y₀₁ hAt₁ u₁ ε₁ hbc₁ l₁ a β₁ hβ₁.symm lam,
      key p₂ y₂ ev₂ hCen₂ hev₂ y₀₂ hAt₂ u₂ ε₂ hbc₂ l₂ a β₂ hβ₂.symm lam]
  by_cases hex : ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p) (_ : M.Cen U₀ x y)
      (_ : spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y) (y₀ : S.R →+* PadicAlgCl p) (_ : S.At M y y₀)
      (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X) (_ : GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε), Nonempty u.Lab
  · obtain ⟨p₁, hp₁, y₁, ev₁, hCen₁, hev₁, y₀₁, hAt₁, u₁, ε₁, hbc₁, ⟨l₁⟩⟩ := hex
    refine ⟨(qmap (S.r * S.N) ε₁.symm).comp l₁.yy, ?_⟩
    intro p _ y ev hCen hev y₀ hAt u ε hbc l a α
    rw [AddMonoidHom.comp_apply, hconst p₁ y₁ ev₁ hCen₁ hev₁ y₀₁ hAt₁ u₁ ε₁ hbc₁ l₁ p y ev hCen hev y₀ hAt u ε hbc l a]
    obtain ⟨β, hβ⟩ := QuotientAddGroup.mk_surjective (l.yy a)
    rw [← hβ, qmap_mk]
    exact mk_symm_eq_iff _ ε β α
  · refine ⟨0, ?_⟩
    intro p _ y ev hCen hev y₀ hAt u ε hbc l
    exact absurd ⟨p, inferInstance, y, ev, hCen, hev, y₀, hAt, u, ε, hbc, ⟨l⟩⟩ hex

end GlobalTheory.Poinc.LabConst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionDescendsFromAlgClosedFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitExpansion_descends_from_algClosed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k) (c : F), c ≠ 0 → (∀ F₀, ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀) → (∀ (F₀ : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F₀, T.Exp a b (Φ F₀) F₀ := by
  first | exact @GlobalTheory.Mum.TraitDescent.exp_of_values | exact GlobalTheory.Mum.TraitDescent.exp_of_values | (intros; apply GlobalTheory.Mum.TraitDescent.exp_of_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCubicalStructureGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_cubical_structure_generic_fibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (c : CubicalStr A.A ⟨A.L, ρ, A.isLB, hρ⟩) (x : Finset (Fin 3) → (TFK (R := V) (FractionRing V) ⟶ A.A)) (h : Finset (Fin 3) → ((𝟙_ (Over (Sp V))) ⟶ G)), x ∅ = 1 → x {0, 1} = x {0} * x {1} → x {0, 2} = x {0} * x {2} → x {1, 2} = x {1} * x {2} → x {0, 1, 2} = x {0} * x {1} * x {2} → h ∅ = 1 → h {0, 1} = h {0} * h {1} → h {0, 2} = h {0} * h {2} → h {1, 2} = h {1} * h {2} → h {0, 1, 2} = h {0} * h {1} * h {2} → (∀ S, IntTerm.Ext U.toUnifPre (x S) (h S)) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1, 2}).left) (fun _ => JA (x {0, 1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}).left) (fun _ => JA (x {0}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}).left) (fun _ => JA (x {1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}).left) (fun _ => JA (x {2}).left)) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x {0}) (x {1}) (x {2})) = cubV U.cubG z JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}) * (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1}).left) (fun _ => JA (x {0, 1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 2}).left) (fun _ => JA (x {0, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1, 2}).left) (fun _ => JA (x {1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x ∅).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h ∅).left) (fun _ => JA (x ∅).left)) := by
  first | exact @GlobalTheory.GenericCube.cube_through_iso | exact GlobalTheory.GenericCube.cube_through_iso | (intros; apply GlobalTheory.GenericCube.cube_through_iso <;> assumption)
end

