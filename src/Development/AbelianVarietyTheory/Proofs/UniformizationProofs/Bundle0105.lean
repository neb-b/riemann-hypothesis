module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsOddNeZero
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZeroOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitPointEqOfIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sabMap_of_iso (hG : GlobalFnsSt) {S S' : Scheme.{0}} {t t' : SAB H S} {u u' : SAB H S'} {f : S' ⟶ S}
    (n : SABMap u t f) (n' : SABMap u' t' f) (hA : IsAbelianScheme u.G) (ψ : t.G ≅ t'.G) [IsMonHom ψ.hom]
    (hact : ∀ x, t.act.act x ≫ ψ.hom = ψ.hom ≫ t'.act.act x) (hL : LBIso t.PP.L (t'.PP.L.pull ψ.hom.left)) :
    ∃ m : SABMap u u' (𝟙 _), m.φ ≫ n'.φ = n.φ ≫ ψ.hom.left := by
  have c := n.cart.comp (isGrpPullback_of_iso ψ)
  rw [Category.comp_id] at c
  obtain ⟨α, hα, hφ⟩ := grpPullback_iso c n'.cart
  have ha : ∀ x, (u.act.act x).left ≫ α.hom.left = α.hom.left ≫ (u'.act.act x).left := fun x => by
    have e : (t.act.act x).left ≫ ψ.hom.left = ψ.hom.left ≫ (t'.act.act x).left := congrArg (fun q => q.left) (hact x)
    apply n'.cart.1.hom_ext
    · rw [Category.assoc, hφ, Category.assoc, n'.act, ← Category.assoc, n.act, ← Category.assoc, hφ, Category.assoc,
        Category.assoc, e]
    · simp only [Category.assoc, Over.w]
  have hb : LBIso u.PP.L (u'.PP.L.pull α.hom.left) := by
    obtain ⟨w, hw⟩ := hL
    obtain ⟨w₁, g₁, -⟩ := (isPullCubical_iff n.cm t.cub u.cub).1 n.lin
    obtain ⟨w₂, g₂, -⟩ := (isPullCubical_iff n'.cm t'.cub u'.cub).1 n'.lin
    have hw' := (isGen_iff w).1 hw
    obtain ⟨w₃, T⟩ := exists_comp t.PP.isLB w w₁ hw' g₁ t'.PP.isLB u.PP.isLB
    obtain ⟨w₄, g₄⟩ : ∃ w₄ : LB.Iso u.PP.L (t'.PP.L.pull (α.hom.left ≫ n'.cm.F)), PGen w₄ := by
      rw [hφ]; exact ⟨w₃, T.pgen_comp t.PP.isLB hw' g₁⟩
    obtain ⟨w₅, T'⟩ := exists_cancel t'.PP.isLB w₂ w₄ g₂ g₄ u'.PP.isLB u.PP.isLB
    exact ⟨w₅, (isGen_iff w₅).2 (T'.pgen_cancel t'.PP.isLB g₂ g₄)⟩
  exact ⟨⟨CubeMap.ofHom α.hom, isGrpPullback_of_iso α, rfl, ha,
    HeckePoint.isPullCubical_of_iso hG hA α.hom u.cub u'.cub hb⟩, hφ⟩

theorem exists_sab_fac {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : h = g ≫ f) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact ObjMaps.exists_sab_cancel m n

variable {D : Datum H} {l : Level H}

theorem objMap_eq (hS : SerreSt) {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {F : Type} [Field F]
    {s : S ⟶ Sp B} {s' : Sp F ⟶ Sp B} {o : Obj D l b s} {o₁ : Obj D l b s'} {y y' : Sp F ⟶ S} (e : y = y')
    (m : ObjMap o₁ o y) (m' : ObjMap o₁ o y') : m.toSABMap.φ = m'.toSABMap.φ := by
  subst e
  exact objMap_unique_of_field hS m m'

theorem point_eq (hL : Laws) {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O']
    {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'} {S : Scheme.{0}} {χ : S ⟶ Y.X}
    {χ' : S ⟶ Y'.X} {t t' : SAB H S} (m : SABMap t Y.t χ) (m' : SABMap t' Y'.t χ') (ψ : t.G ≅ t'.G) [IsMonHom ψ.hom]
    (hact : ∀ x, t.act.act x ≫ ψ.hom = ψ.hom ≫ t'.act.act x) (hb : LBIso t.PP.L (t'.PP.L.pull ψ.hom.left))
    {K : Type} [Field K] (j : Sp K ⟶ S) (y y' : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = j ≫ χ) (hy' : y' ≫ Y'.j = j ≫ χ')
    (hs : y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _)
    (hlev : ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G),
      ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) →
      ∀ g : Sp K ⟶ t.G.left, g ≫ t.G.hom = j → g ≫ m.φ = y ≫ σ.left ≫ Y.m.φ →
        g ≫ ψ.hom.left ≫ m'.φ = y' ≫ σ'.left ≫ Y'.m.φ) :
    y = y' ∧ ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left) (τ : T ⟶ Sp K),
      g ≫ t.G.hom = τ ≫ j → g₁ ≫ Y.oF.t.G.hom = τ ≫ y → g ≫ m.φ = g₁ ≫ Y.m.φ →
      g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom →
      g ≫ ψ.hom.left ≫ m'.φ = g₂ ≫ Y'.m.φ := by
  have hid : spMap (RingHom.id (KA l)) = 𝟙 _ := Spec.map_id _
  have hs' : y' ≫ pullback.fst _ _ ≫ Xo.s = y ≫ pullback.fst _ _ ≫ Xo.s := by
    rw [pullback.condition, reassoc_of% hs]
  obtain ⟨o, ⟨m₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ (y ≫ pullback.fst _ _ ≫ Xo.s) y
    rfl rfl (by rw [hid, Category.comp_id]) Y.oF
  obtain ⟨o', ⟨m₂⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ (y ≫ pullback.fst _ _ ≫ Xo.s) y'
    rfl rfl (by rw [hid, Category.comp_id, hs']) Y'.oF
  obtain ⟨k₁, e₁⟩ := ObjMaps.exists_sab_comp Y.m m₁.toSABMap
  obtain ⟨k₂, e₂⟩ := ObjMaps.exists_sab_comp Y'.m m₂.toSABMap
  obtain ⟨n, hn⟩ := exists_sab_fac m k₁ hy
  obtain ⟨n', hn'⟩ := exists_sab_fac m' k₂ hy'
  obtain ⟨ν, hν⟩ := exists_sabMap_of_iso hL.globalFns n n'
    ⟨inferInstance, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩ ψ hact hb
  have hνw : ν.φ ≫ o'.t.G.hom = o.t.G.hom := ν.cart.1.w.trans (Category.comp_id _)
  have hψ : n.φ ≫ ψ.hom.left ≫ m'.φ = ν.φ ≫ m₂.toSABMap.φ ≫ Y'.m.φ := by
    rw [← e₂, hn', reassoc_of% hν]
  have key : ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G)
      (x : 𝟙_ (Over (Sp K)) ⟶ o.t.G) (x' : 𝟙_ (Over (Sp K)) ⟶ o'.t.G),
      ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) →
      x.left ≫ m₁.toSABMap.φ = y ≫ σ.left → x'.left ≫ m₂.toSABMap.φ = y' ≫ σ'.left →
      x.left ≫ ν.φ = 𝟙 _ ≫ x'.left := by
    intro σ σ' x x' h hx hx'
    have b : x.left ≫ o.t.G.hom = 𝟙 _ := Over.w x
    have b' : x'.left ≫ o'.t.G.hom = 𝟙 _ := Over.w x'
    have q := hlev σ σ' h (x.left ≫ n.φ) (by rw [Category.assoc, n.cart.1.w, reassoc_of% b])
      (by rw [Category.assoc, ← hn, e₁, reassoc_of% hx])
    rw [Category.id_comp]
    apply k₂.cart.1.hom_ext
    · show (_ ≫ _) ≫ k₂.φ = _ ≫ k₂.φ
      rw [e₂, Category.assoc, ← hψ, reassoc_of% hx', ← q, Category.assoc]
    · rw [Category.assoc, hνw, b, b']
  let ν' : ObjMap o o' (𝟙 _) :=
    ⟨ν, fun a => key _ _ _ _ (Or.inr ⟨a, rfl, rfl⟩) (m₁.eta a) (m₂.eta a),
      fun a => key _ _ _ _ (Or.inl ⟨a, rfl, rfl⟩) (m₁.etaA a) (m₂.etaA a)⟩
  obtain ⟨p₁, f₁⟩ := ObjComp.objMap_comp Y.m0 m₁
  obtain ⟨p₀, f₀⟩ := ObjComp.objMap_comp m₂ ν'
  obtain ⟨p₂, f₂⟩ := ObjComp.objMap_comp Y'.m0 p₀
  have hf := (Xo.rep _ _ inferInstance o).unique ⟨Category.assoc _ _ _, ⟨p₁⟩⟩
    ⟨by rw [Category.id_comp, Category.assoc, hs'], ⟨p₂⟩⟩
  have hp : m₁.toSABMap.φ ≫ Y.m0.toSABMap.φ = (ν.φ ≫ m₂.toSABMap.φ) ≫ Y'.m0.toSABMap.φ :=
    f₁.symm.trans ((objMap_eq hL.serre hf p₁ p₂).trans (f₂.trans (congrArg (· ≫ _) f₀)))
  rw [Category.id_comp] at hf
  obtain rfl : y = y' := pullback.hom_ext hf hs
  refine ⟨rfl, fun T g g₁ g₂ τ h₁ h₂ h₃ h₄ h₅ => ?_⟩
  obtain ⟨u, u₁, u₂⟩ : ∃ u : T ⟶ o.t.G.left, u ≫ m₁.toSABMap.φ = g₁ ∧ u ≫ o.t.G.hom = τ :=
    ⟨m₁.cart.1.lift g₁ τ h₂, m₁.cart.1.lift_fst _ _ _, m₁.cart.1.lift_snd _ _ _⟩
  have a₁ : u ≫ n.φ = g := by
    apply m.cart.1.hom_ext
    · show (_ ≫ _) ≫ m.φ = _ ≫ m.φ
      rw [Category.assoc, ← hn, e₁, reassoc_of% u₁, h₃]
    · rw [Category.assoc, n.cart.1.w, reassoc_of% u₂, h₁]
  have a₂ : u ≫ ν.φ ≫ m₂.toSABMap.φ = g₂ := by
    apply Y'.m0.cart.1.hom_ext
    · show (_ ≫ _) ≫ Y'.m0.toSABMap.φ = _ ≫ Y'.m0.toSABMap.φ
      rw [Category.assoc, ← hp, reassoc_of% u₁, h₄]
    · rw [Category.assoc, Category.assoc, m₂.cart.1.w, reassoc_of% hνw, reassoc_of% u₂, ← h₅, h₂]
  rw [← a₁, ← a₂, Category.assoc, hψ, Category.assoc, Category.assoc]

end ArcObj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfFiniteOrderOfFixThreeTorsion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.FiniteOrderFix


open TorsionZero in
theorem exists_sec_le {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp K) {L : LB X}
    (hL : L.IsLB) {N : ℕ} {σ : Type} (s : σ → (lbPow L N).Sec)
    (hcov : ⨆ i, nonzeroLocus (s i) = ⊤) (haff : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, σ → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k, resG X (inf_le_right : nonzeroLocus (s i) ⊓ (lbPow L N).U k ≤ _) ((s j).f k) =
      resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
    (hgen : ∀ i (f : Γ(X, nonzeroLocus (s i))), ∃ F : MvPolynomial σ K,
      f = MvPolynomial.eval₂ (constHom p _) (r i) F)
    (U : X.Opens) (hU : genericPoint X ∈ U) :
    ∃ (d : ℕ) (u : (lbPow L (N * d)).Sec), (∃ j, u.f j ≠ 0) ∧
      ∀ z : Sp K ⟶ X, z ≫ p = 𝟙 _ → ⊤ ≤ z ⁻¹ᵁ nonzeroLocus u → ⊤ ≤ z ⁻¹ᵁ U := by
  obtain ⟨R, _, _, _, 𝒜, _, Φ, -, -, -, hρ⟩ := SectionRing.exists_sectionRing K X p L hL
  choose ρ hρc hρ using hρ
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ nonzeroLocus (s i) :=
    TopologicalSpace.Opens.mem_iSup.1 (by rw [hcov]; trivial)
  letI : Algebra K Γ(X, nonzeroLocus (s i)) := (constHom p _).toAlgebra
  obtain ⟨h1, h2, -⟩ := chart_facts p Φ ρ hL hρc hρ s i hi (fun _ => rfl) (r i) (hr i) (fun f => by
    obtain ⟨F, hF⟩ := hgen i f
    exact ⟨F, hF.symm⟩)
  obtain ⟨f, hfU, hf⟩ := (haff i).exists_basicOpen_le ⟨_, hU⟩ hi
  obtain ⟨F, hF⟩ := hgen i f
  obtain ⟨n, G, hG, hGF⟩ := exists_homogenisation F i
  have hG' : (G * MvPolynomial.X i).IsHomogeneous (n + 1) := hG.mul (MvPolynomial.isHomogeneous_X K i)
  have hGf : MvPolynomial.aeval (r i) G = f := (hGF _ (r i) h1).trans hF.symm
  have hm := aeval_mem_of_isHomogeneous 𝒜 (fun j => (Φ N (s j)).2) hG'
  obtain ⟨u, hu⟩ := (Φ (N * (n + 1))).surjective ⟨_, hm⟩
  have hu' : (Φ _ u : R) = MvPolynomial.aeval (fun j => (Φ N (s j) : R)) (G * MvPolynomial.X i) :=
    congrArg Subtype.val hu
  refine ⟨n + 1, u, ?_, fun z hz hzu => ?_⟩
  · by_contra h0
    have h3 := eq_zero_of_not_mem Φ ρ hL hρ u fun h => by
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have e : u.f k = 0 := by_contra fun e => h0 ⟨k, e⟩
      rw [e, Scheme.basicOpen_zero] at hk
      exact hk
    have h4 := (h2 _ _ hG').1 (hu'.symm.trans h3)
    rw [map_mul, MvPolynomial.aeval_X, h1, _root_.mul_one, hGf] at h4
    rw [h4, Scheme.basicOpen_zero] at hf
    exact hf
  · obtain ⟨ev, hev, hevr⟩ := exists_ev p Φ ρ hL hρc hρ z hz
    have h3 := (hev _ u).2 hzu
    rw [hu', map_mul, map_mul, MvPolynomial.aeval_X, mul_ne_zero_iff] at h3
    have hzi := (hev _ (s i)).1 h3.2
    let v : Γ(X, nonzeroLocus (s i)) →ₐ[K] K :=
      { TorsionZero.val z _ hzi with commutes' := fun a => val_const p z hz _ hzi a }
    have h4 := h3.1
    rw [MvPolynomial.comp_aeval_apply, funext fun j => hevr N (s j) (s i) _ hzi (r i j) (hr i j),
      aeval_mul_of_isHomogeneous _ _ hG, mul_ne_zero_iff] at h4
    have h5 : v f ≠ 0 := by
      rw [← hGf, MvPolynomial.comp_aeval_apply]
      exact h4.1
    exact fun y hy => hfU ((val_ne_zero_iff z _ hzi f).1 h5 hy)

theorem eq_of_agree_on_pow_torsion (h : Laws) {K : Type} [Field K] [IsAlgClosed K] (P P' : PolAV (Sp K))
    {q : ℕ} (hq : 2 ≤ q) (hqK : (q : K) ≠ 0) (f f' : P.A ⟶ P'.A)
    (hf : ∀ (k : ℕ) (x : baseOver (Sp K) ⟶ P.A), x ^ q ^ k = 1 → x ≫ f = x ≫ f') : f = f' := by
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · exact EndOnTorsion.eq_of_dim_zero P P' hg _ _ (hf 0 1 (one_pow _))
  have := polAV_isIntegral_of_isAlgClosed K P
  have := P'.isAb.proper
  have hw : f.left ≫ P'.A.hom = f'.left ≫ P'.A.hom := (Over.w f).trans (Over.w f').symm
  have := isClosedImmersion_equalizer_ι_of_isSeparated P'.A.hom hw
  let U : P.A.left.Opens := ⟨(Set.range (equalizer.ι f.left f'.left))ᶜ,
    (equalizer.ι f.left f'.left).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : genericPoint P.A.left ∉ U := fun hU => by
    obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow h.ample K P 4 le_rfl
    choose haff r hr hgen using hs
    obtain ⟨d, u, hu, hz⟩ := exists_sec_le P.A.hom P.isLB s hcov haff r hr hgen U hU
    obtain ⟨k, hk⟩ : ∃ k, 4 ^ P.g * P.g.factorial * d < (q ^ k) ^ 2 :=
      ⟨_, (Nat.lt_pow_self hq).trans_le (Nat.le_self_pow two_ne_zero _)⟩
    have hM : ((q ^ k : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hqK
    have hM1 : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
    have hcard := (h.mulN (Sp K) P _ hM1).2.2.2.2 K (𝟙 _) hM
    have h₄ := card_zeros_on_torsion_coset_le h.mulN SectionRing.exists_sectionRing
      (PowSec.exists_basis_sections h.globalSectionsRank) (veryAmple_lbPow h.ample) (exists_mulPull_sec h.mulPull)
      SmoothDim.ringKrullDim_affineOpen polAV_isIntegral_of_isAlgClosed isIntegral_adjoin_of_mul_pow_mem
      graded_bezout_bound K P 4 d (q ^ k) 1 hg le_rfl hM u hu
    have h₅ : ∀ x : baseOver (Sp K) ⟶ P.A, x ^ q ^ k = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ nonzeroLocus u :=
      fun x hx hx' => (TorsionZero.top_le_iff x.left _).1 (hz x.left (Over.w x) hx')
        (range_subset_range_equalizer_ι x.left (congrArg (·.left) (hf k x hx)) ⟨_, rfl⟩)
    have e : (q ^ k) ^ (2 * P.g) = (q ^ k) ^ 2 * (q ^ k) ^ (2 * P.g - 2) := by
      rw [← pow_add]; congr 1; omega
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => and_iff_left_of_imp (h₅ x)), hcard, e] at h₄
    exact absurd (Nat.le_of_mul_le_mul_right h₄ (pow_pos hM1 _)) (not_le.2 hk)
  have : IsDominant (equalizer.ι f.left f'.left) := ⟨dense_iff_closure_eq.2 (top_unique
    ((genericPoint_spec P.A.left).def.ge.trans (closure_mono (Set.singleton_subset_iff.2 (not_not.1 hU)))))⟩
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated P'.A.hom hw _ (equalizer.condition _ _))


open SerreField in
theorem eq_one_of_field (h : Laws) {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K))
    {M : ℕ} (hM : 3 ≤ M) (σ : CategoryTheory.End P.A) [hσ : IsMonHom σ.asHom] {m : ℕ} (hm : m ≠ 0)
    (hord : σ ^ m = 1) (hfix : ∀ x : baseOver (Sp K) ⟶ P.A, x ^ M = 1 → x ≫ σ.asHom = x) : σ = 1 := by
  have hdiv := DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one (fun S _ P n hn =>
    ⟨(h.mulN S P n hn).1, (h.mulN S P n hn).2.1, (h.mulN S P n hn).2.2.1, (h.mulN S P n hn).2.2.2.1⟩)
  have hfix' := fix_torsion_of_fix_geometric_of_isDominant h.mulN P M (by omega) (by
    simpa using (Nat.cast_ne_zero.2 (by omega) : (M : K) ≠ 0).isUnit.map
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) (𝟙 _) σ.asHom hσ hfix
  let τ : P.A ⟶ P.A := σ.asHom
  have hu : IsMonHom (τ * (𝟙 P.A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨⟨φ, hφ, e⟩, -⟩ := hdiv _ P P.A M (by omega) (τ * (𝟙 P.A)⁻¹) hu (fun T x hx => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hfix' T x hx, Category.comp_id, mul_inv_cancel])
  have hpow : ∀ (n : ℕ) (x : P.A ⟶ P.A), (toRing τ ^ n).1 (Additive.ofMul x) =
      Additive.ofMul (x ≫ (σ ^ n).asHom) := fun n x => by
    induction n with
    | zero => exact congrArg Additive.ofMul (Category.comp_id x).symm
    | succ n ih =>
      rw [pow_succ', pow_succ', End.mul_asHom, ← Category.assoc]
      exact (congrArg (toRing τ).1 ih).trans (toRing_apply _ _)
  have key : toRing τ = 1 := by
    refine eq_one_of_pow_eq_one_of_congr_one (homRing P.A) M hM ?_ ?_ (toRing τ) (toRing φ) m hm ?_ ?_
    · rintro k ⟨f, u, hu, hf⟩ hk e
      have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e
      simp only [natCast_mul_apply, hf, Category.id_comp] at h1
      have h2 : u ^ k = 1 := h1
      obtain ⟨_, _, _, -⟩ := h.mulN _ P k (by omega)
      have h3 : u = 1 := DivisibleHom.cancel_of_flat_surjective (mulA P.A k)
        (by rw [DivisibleHom.mulA_comp, h2, MonObj.comp_one])
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · rintro q ⟨f, u, hu, hf⟩ hq e
      have h3 : u = 1 := eq_of_agree_on_pow_torsion h P P hq (Nat.cast_ne_zero.2 (by omega)) u 1
        fun k x hx => by
          obtain ⟨⟨g, v, hv, hg⟩, e⟩ := e k
          have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e
          simp only [← Nat.cast_pow, natCast_mul_apply, hf, hg, Category.id_comp] at h1
          have h2 : u = v ^ q ^ k := h1
          rw [h2, MonObj.comp_pow, ← MonObj.pow_comp, hx, MonObj.one_comp, MonObj.comp_one]
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · refine homRing_ext ?_
      change _ = Additive.ofMul (𝟙 P.A) + ((M : homRing P.A) * toRing φ).1 _
      rw [natCast_mul_apply, toRing_apply, toRing_apply, Category.id_comp, Category.id_comp,
        ← ofMul_pow, ← e, ← ofMul_mul, mul_comm, inv_mul_cancel_right]
    · exact homRing_ext (by rw [hpow, hord, End.one_asHom, Category.id_comp]; rfl)
  have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) key
  simp only [toRing_apply, Category.id_comp] at h1
  exact End.ext h1

theorem eq_one_of_finite_order_of_fix_three_torsion :
    LL → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] [CharZero F]
      (p : Spec (CommRingCat.of F) ⟶ S) (h : CategoryTheory.End (Over.mk p ⊗ P.A)),
      h.asHom ≫ fst _ _ = fst _ _ → ptSecT P.A 1 ≫ h.asHom = ptSecT P.A 1 →
      (∃ n, 1 ≤ n ∧ h ^ n = 1) →
      (∀ x : Over.mk p ⟶ P.A, x ^ 3 = 1 → ptSecT P.A x ≫ h.asHom = ptSecT P.A x) → h = 1 := by
  rintro ⟨laws, -⟩ S _ P F _ _ _ p h hfst h0 ⟨n, hn, hord⟩ hfix
  obtain ⟨P', g, hg, -, pm, -⟩ := laws.polBaseChange S _ p P
  have hg' : IsPullback (snd (Over.mk p) P.A).left (fst (Over.mk p) P.A).left P.A.hom p :=
    (IsPullback.of_hasPullback p P.A.hom).flip
  let e := hg.isoIsPullback _ _ hg'
  have e₁ : e.hom ≫ (snd (Over.mk p) P.A).left = g := hg.isoIsPullback_hom_fst _ _ hg'
  have e₂ : e.hom ≫ (fst (Over.mk p) P.A).left = P'.A.hom := hg.isoIsPullback_hom_snd _ _ hg'
  have e₃ : h.asHom.left ≫ (fst (Over.mk p) P.A).left = (fst (Over.mk p) P.A).left := congrArg (·.left) hfst
  let σ : CategoryTheory.End P'.A := End.of (Over.homMk (e.hom ≫ h.asHom.left ≫ e.inv) (by
    rw [← e₂, Category.assoc, Category.assoc, e.inv_hom_id_assoc, e₃]))
  have hσ : σ.asHom.left ≫ e.hom = e.hom ≫ h.asHom.left := by
    change (e.hom ≫ h.asHom.left ≫ e.inv) ≫ e.hom = _
    simp
  have hpow : ∀ k : ℕ, (σ ^ k).asHom.left ≫ e.hom = e.hom ≫ (h ^ k).asHom.left := fun k => by
    induction k with
    | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | succ k ih =>
      rw [pow_succ', pow_succ', End.mul_asHom, End.mul_asHom, Over.comp_left, Over.comp_left, Category.assoc, hσ,
        reassoc_of% ih]
  let c : Over.mk p ⟶ Over.mk ((baseOver (Sp F)).hom ≫ p) := Over.homMk (𝟙 _) (by simp)
  let ρ : (baseOver (Sp F) ⟶ P'.A) →* (Over.mk p ⟶ P.A) := MonoidHom.mk' (fun x => c ≫ toBase hg.w x)
    fun x y => by rw [pm, MonObj.comp_mul]
  have hρ : ∀ x, (ptSecT P.A (ρ x)).left = x.left ≫ e.hom := fun x => by
    refine hg'.hom_ext ?_ ?_
    · rw [← Over.comp_left, ptSecT, lift_snd, Category.assoc, e₁]
      exact Category.id_comp _
    · rw [← Over.comp_left, ptSecT, lift_fst, Category.assoc, e₂]
      exact (Over.w x).symm
  have key : ∀ x, ptSecT P.A (ρ x) ≫ h.asHom = ptSecT P.A (ρ x) → x ≫ σ.asHom = x := fun x hx => by
    have := congrArg (·.left) hx
    simp only [Over.comp_left, hρ] at this
    refine Over.OverMorphism.ext ((cancel_mono e.hom).1 ?_)
    rw [Over.comp_left, Category.assoc, hσ, ← Category.assoc, this]
  have hη : (1 : baseOver (Sp F) ⟶ P'.A) = η[P'.A] :=
    (congrArg (· ≫ η[P'.A]) toUnit_unit).trans (Category.id_comp _)
  have : IsMonHom σ.asHom := laws.rigidity _ _ _ P'.isAb P'.isAb σ.asHom (by
    have := key 1 (by rw [map_one]; exact h0)
    rwa [hη] at this)
  have h1 : σ = 1 := eq_one_of_field laws P' le_rfl σ (m := n) (by omega)
    (End.ext (Over.OverMorphism.ext ((cancel_mono e.hom).1 ((hpow n).trans (by rw [hord]; exact (hpow 0).symm)))))
    fun x hx => key x (hfix _ (by rw [← map_pow, hx, map_one]))
  refine End.ext (Over.OverMorphism.ext ((cancel_epi e.hom).1 ?_))
  rw [← hσ, h1]
  exact hpow 0

end GlobalTheory.FiniteOrderFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroClosedFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpreadSec

variable {X X' : Scheme.{0}}

theorem exists_pull {M : LB X} (s : LB.Sec M) (π : X' ⟶ X) :
    ∃ t : LB.Sec (M.pull π), ∀ (j : (M.pull π).ι) (z : X'), π z ∈ M.U (j PUnit.unit) →
      gs (𝟙 X') z _ (t.f j) = gs π z _ (s.f (j PUnit.unit)) := by
  let a : ∀ j : (M.pull π).ι, Γ(X', (M.pull π).U j) := fun j =>
    rs X' (LB.wchart_le M (fun _ : PUnit => π) j PUnit.unit) ((π.app _).hom (s.f (j PUnit.unit)))
  have ha : ∀ (j : (M.pull π).ι) (z : X'), π z ∈ M.U (j PUnit.unit) →
      gs (𝟙 X') z _ (a j) = gs π z _ (s.f (j PUnit.unit)) := fun j z hz => by
    have hm : (𝟙 X' : X' ⟶ X') z ∈ (M.pull π).U j := Set.mem_iInter.2 fun _ => hz
    refine (gs_res (𝟙 X') z _ hm _).trans ?_
    rw [gs_pull (𝟙 X') π z _ hz, Category.id_comp]
  refine ⟨⟨a, fun i j => fn_ext fun z hz => ?_⟩, ha⟩
  have hi : π z ∈ M.U (i PUnit.unit) := Set.mem_iInter.1 hz.1 PUnit.unit
  have hj : π z ∈ M.U (j PUnit.unit) := Set.mem_iInter.1 hz.2 PUnit.unit
  refine ((gs_res (𝟙 X') z _ hz _).trans (ha i z hi)).trans (Eq.trans ?_ ((gs_mul (𝟙 X') z _ hz _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 X') z _ hz _).trans
      (congrArg Units.val (gm_linComb M _ _ (𝟙 X') z i j hz.1 hz.2))) ((gs_res (𝟙 X') z _ hz _).trans
        (ha j z hj)))).symm)
  rw [FlatSec.gs_sec_trans s π z hi hj, Fintype.prod_unique, zpow_one, Category.id_comp]

theorem app_eq_zero {M : LB X} {π : X' ⟶ X} (h : ∀ (t : LB.Sec (M.pull π)) j, t.f j = 0) (s : LB.Sec M) (k : M.ι) :
    (π.app _).hom (s.f k) = 0 := by
  obtain ⟨t, ht⟩ := exists_pull s π
  refine fn_ext fun z hz => ?_
  have hz' : π z ∈ M.U k := hz
  rw [gs_pull (𝟙 X') π z _ hz', Category.id_comp, ← ht (fun _ => k) z hz',
    LBGerm.gs_zero (𝟙 X') z _ hz]
  refine (congrArg (gs (𝟙 X') z _) (h t fun _ => k)).trans ?_
  exact LBGerm.gs_zero (𝟙 X') z _ (Set.mem_iInter.2 fun _ => hz')

theorem exists_ne_zero_closed_fibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom] (N : LB G.left), N.IsLB → (∃ s : LB.Sec (N.pull (pullback.fst G.hom (jK V))), (∃ j, s.f j ≠ 0)) → ∃ s : LB.Sec (N.pull (fstG (IsLocalRing.maximalIdeal V) 0 G).left), (∃ j, s.f j ≠ 0) := by
  intro V _ _ _ G _ _ _ _ _ N hN ⟨s, j, hj⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have h0 : ∀ σ : LB.Sec N, ∃ τ : LB.Sec N, DVR.SecIsMul G.hom (ϖ ^ (0 + 1)) σ τ := fun σ =>
    (ThickDiv.main V ϖ hϖ G N σ 0).1 (app_eq_zero hcon σ)
  have h1 : ∀ (n : ℕ) (σ : LB.Sec N), ∃ τ : LB.Sec N, DVR.SecIsMul G.hom (ϖ ^ (n + 1)) σ τ := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      intro σ
      obtain ⟨τ, hτ⟩ := ih σ
      obtain ⟨ρ, hρ⟩ := h0 τ
      refine ⟨ρ, fun k => ?_⟩
      have e₁ : σ.f k = AbLaw.cst G.hom _ (ϖ ^ (n + 1)) * τ.f k := hτ k
      have e₂ : τ.f k = AbLaw.cst G.hom _ (ϖ ^ (0 + 1)) * ρ.f k := hρ k
      change σ.f k = AbLaw.cst G.hom _ (ϖ ^ (n + 1 + 1)) * ρ.f k
      rw [e₁, e₂, ← _root_.mul_assoc, ← map_mul, ← pow_add]
  have h2 : ∀ (σ : LB.Sec N) k, σ.f k = 0 := fun σ =>
    (sec_eq_zero_and_hom_eq_of_thickenings V (IsLocalRing.maximalIdeal V)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge G).1 N hN σ fun n =>
        (ThickDiv.main V ϖ hϖ G N σ n).2 (h1 n σ)
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat V (FractionRing V) (algebraMap V _)
    (RingHom.flat_algebraMap_iff.2 inferInstance) G.left G.hom _ _ _
    (IsPullback.of_hasPullback G.hom (jK V)) N hN s
  refine hj (fn_ext fun z hz => ?_)
  have hz' : pullback.fst G.hom (jK V) z ∈ N.U (j PUnit.unit) := Set.mem_iInter.1 hz PUnit.unit
  rw [LBGerm.gs_zero _ z _ hz]
  refine (hu z (j PUnit.unit) hz').trans (Finset.sum_eq_zero fun i _ => ?_)
  rw [h2, LBGerm.gs_zero _ z _ hz', mul_zero]

end GlobalTheory.SpreadSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducedFrobeniusCompUniqueOriginStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indAt_comp_equiv_unique_id : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p p' p'' : QkPt D.toPre F N) (ψ ψ' : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)), IndAt U.toUnifPre F N p ψ → (IndAt U.toUnifPre F N p' ψ' → QkAdd p p' p'' → IndAt U.toUnifPre F N p'' (ψ ≫ ψ')) ∧ (QkPt.Equiv D.toPre F p p' → IndAt U.toUnifPre F N p' ψ) ∧ (4 ≤ N → IndAt U.toUnifPre F N p ψ' → ψ = ψ') ∧ (p'.y = 0 → p'.g.IsZero → IndAt U.toUnifPre F N p' (𝟙 _)) := by
  first | exact @GlobalTheory.UT.IndComp.indAt_comp_unique | exact GlobalTheory.UT.IndComp.indAt_comp_unique | (intros; apply GlobalTheory.UT.IndComp.indAt_comp_unique <;> assumption)
end

