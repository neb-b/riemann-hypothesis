module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2863
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationLogDerivativeCechCocycle
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KappaCoc

theorem resG_resG' (Z : Scheme.{0}) {U V O : Z.Opens} (h : V ≤ U) (h' : O ≤ V) (f : Γ(Z, U)) :
    resG Z h' (resG Z h f) = resG Z (h'.trans h) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem dlog_cocycle {Z : Scheme.{0}} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hd : IsField W₀ d)
    (L : LB Z) (hL : L.IsLB) {a b c : L.ι} {W₁ W₂ W₃ : Z.Opens} (h₁ : W₁ ≤ L.U a) (h₂ : W₂ ≤ L.U b)
    (h₃ : W₃ ≤ L.U c) (hW₁ : W₁ ≤ W₀) (hW₂ : W₂ ≤ W₀) :
    resG Z (inf_le_left : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₂) (d (W₁ ⊓ W₂) (resG Z (inf_le_inf h₁ h₂) (L.g a b).val) *
        resG Z (inf_le_inf h₁ h₂) (L.g a b)⁻¹.val) +
      resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂ ⊓ W₃)
        (d (W₂ ⊓ W₃) (resG Z (inf_le_inf h₂ h₃) (L.g b c).val) * resG Z (inf_le_inf h₂ h₃) (L.g b c)⁻¹.val) =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₃)
        (d (W₁ ⊓ W₃) (resG Z (inf_le_inf h₁ h₃) (L.g a c).val) * resG Z (inf_le_inf h₁ h₃) (L.g a c)⁻¹.val) := by
  have l₁ : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₂ := inf_le_left
  have l₂ : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂ ⊓ W₃ := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l₃ : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₃ := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hV : W₁ ⊓ W₂ ⊓ W₃ ≤ W₀ := inf_le_left.trans (inf_le_left.trans hW₁)
  have lU : W₁ ⊓ W₂ ⊓ W₃ ≤ L.U a ⊓ L.U b ⊓ L.U c := inf_le_inf (inf_le_inf h₁ h₂) h₃
  have comm : ∀ {O : Z.Opens} (h : W₁ ⊓ W₂ ⊓ W₃ ≤ O), O ≤ W₀ → ∀ x : Γ(Z, O),
      resG Z h (d O x) = d _ (resG Z h x) := fun h hO x => (hd.2.2 _ _ h hO x).symm
  rw [map_mul, map_mul, map_mul, comm l₁ (inf_le_left.trans hW₁), comm l₂ (inf_le_left.trans hW₂),
    comm l₃ (inf_le_left.trans hW₁), resG_resG', resG_resG', resG_resG', resG_resG', resG_resG', resG_resG']
  have uv : ∀ {p q : L.ι} (h : W₁ ⊓ W₂ ⊓ W₃ ≤ L.U p ⊓ L.U q),
      resG Z h (L.g p q).val * resG Z h (L.g p q)⁻¹.val = 1 := fun h => by
    rw [← map_mul, Units.mul_inv, map_one]
  have co := congrArg (fun u : Γ(Z, L.U a ⊓ L.U b ⊓ L.U c)ˣ => resG Z lU u.val) (hL.cocycle a b c)
  simp only [Units.val_mul, map_mul] at co
  change resG Z lU (resG Z _ (L.g a b).val) * resG Z lU (resG Z _ (L.g b c).val) =
    resG Z lU (resG Z _ (L.g a c).val) at co
  rw [resG_resG', resG_resG', resG_resG'] at co
  have e := hd.2.1 _ hV (resG Z (l₁.trans (inf_le_inf h₁ h₂)) (L.g a b).val)
    (resG Z (l₂.trans (inf_le_inf h₂ h₃)) (L.g b c).val)
  rw [co] at e
  have ua := uv (l₁.trans (inf_le_inf h₁ h₂))
  have ub := uv (l₂.trans (inf_le_inf h₂ h₃))
  have uc := uv (l₃.trans (inf_le_inf h₁ h₃))
  set A := resG Z (l₁.trans (inf_le_inf h₁ h₂)) (L.g a b).val
  set B := resG Z (l₂.trans (inf_le_inf h₂ h₃)) (L.g b c).val
  set C := resG Z (l₃.trans (inf_le_inf h₁ h₃)) (L.g a c).val
  set A' := resG Z (l₁.trans (inf_le_inf h₁ h₂)) (L.g a b)⁻¹.val
  set B' := resG Z (l₂.trans (inf_le_inf h₂ h₃)) (L.g b c)⁻¹.val
  set C' := resG Z (l₃.trans (inf_le_inf h₁ h₃)) (L.g a c)⁻¹.val
  set dA := d _ A
  set dB := d _ B
  set dC := d _ C
  linear_combination (-C') * e - (dA * A' * C' + dB * B' * C') * co + dA * B * C' * ua + dB * A * C' * ub -
    (dA * A' + dB * B') * uc

end GlobalTheory.KappaCoc

theorem GlobalTheory.KappaCoc.kappa_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)), ∀ (b : Fin n) (i i' i'' : J), resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (δ b (W i' ⊓ W i'') (resG t.G.left (inf_le_inf (hj i') (hj i'')) (t.PP.L.g (j i') (j i'')).val) * resG t.G.left (inf_le_inf (hj i') (hj i'')) (t.PP.L.g (j i') (j i''))⁻¹.val) = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (δ b (W i ⊓ W i'') (resG t.G.left (inf_le_inf (hj i) (hj i'')) (t.PP.L.g (j i) (j i'')).val) * resG t.G.left (inf_le_inf (hj i) (hj i'')) (t.PP.L.g (j i) (j i''))⁻¹.val) := by
  intro E _ _ _ H X t U n δ hδ J W j _ _ hWU hj b i i' i''
  exact GlobalTheory.KappaCoc.dlog_cocycle (hδ b) t.PP.L t.PP.isLB (hj i) (hj i') (hj i'') (hWU i) (hWU i')
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationVectorBundleAbelianPullback
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.Twist (resM)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt.Fibre

section Frames

variable {X Y : Scheme.{0}} {I : Type} [Fintype I] {k : Type} [CommRing k]

theorem frame_pb (f : Y ⟶ X) {F : X.Modules} [F.IsQuasicoherent] {U : X.Opens} {e : I → Γ(F, U)} (he : IsFrame e)
    {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) : IsFrame fun i => pullbackSections f F h (e i) := by
  have := (he.pullback f).res h
  exact (funext fun l => QCoh.res_pullbackSections f F le_rfl h (e l)) ▸ this

end Frames

section Reads

variable {X T : Scheme.{0}} {R K : Type} [CommRing R] [Field K] [Algebra R K] {f : Sp R ⟶ X} {f₀ : T ⟶ X}
  {ξ : Sp K ⟶ T} (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) {I : Type} [Fintype I] {U : X.Opens} {V : T.Opens}
  (hU : ⊤ ≤ f ⁻¹ᵁ U) (hVU : V ≤ f₀ ⁻¹ᵁ U) (hξ : ⊤ ≤ ξ ⁻¹ᵁ V)


variable {H : Type*} [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H]

variable {A B : X.Modules} {D : T.Modules} [A.IsQuasicoherent] [B.IsQuasicoherent] [D.IsQuasicoherent]
  {a : (Scheme.Modules.pullback f₀).obj A ⟶ D} {b : D ⟶ (Scheme.Modules.pullback f₀).obj B} {z : a ≫ b = 0}


end Reads

section Tangent

open GlobalTheory.TanFibre GlobalTheory.Conormal
open GlobalTheory.DeRhamSheaf (onAff)
open GlobalTheory.Published.AbelianDeRham (bcMor)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)

theorem omegaBase_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {f' : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (h : IsGrpPullback G' G f φ) (h' : IsGrpPullback G'' G' f' φ') {f'' : S'' ⟶ S} {φ'' : G''.left ⟶ G.left}
    (h'' : IsGrpPullback G'' G f'' φ'') (e : f' ≫ f = f'') (e' : φ' ≫ φ = φ'') {U : S.Opens} {V : S'.Opens}
    {W : S''.Opens} (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ f' ⁻¹ᵁ V) (hW' : W ≤ f'' ⁻¹ᵁ U) (s : Γ(omega G, U)) :
    (omegaBase h').app W (pullbackSections f' _ hW ((omegaBase h).app V (pullbackSections f _ hV s))) =
      (omegaBase h'').app W (pullbackSections f'' _ hW' s) := by
  subst e e'
  have k {U : S.Opens} {V : S'.Opens} {W : S''.Opens} (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ f' ⁻¹ᵁ V)
      (hW' : W ≤ (f' ≫ f) ⁻¹ᵁ U) (s : Γ(omega G, U)) :
      ((Scheme.Modules.pullbackComp f' f).inv.app (omega G) ≫ (Scheme.Modules.pullback f').map (omegaBase h) ≫
        omegaBase h').app W (pullbackSections (f' ≫ f) _ hW' s) =
      (omegaBase h').app W (pullbackSections f' _ hW ((omegaBase h).app V (pullbackSections f _ hV s))) := by
    rw [← QCoh.app_app, ← QCoh.app_app, Vert.DivPull.pullbackComp_inv_app f' f _ hV hW]
    exact congrArg _ (QCoh.pullback_map_app_pullbackSections f' _ _ _)
  have : (Scheme.Modules.pullbackComp f' f).inv.app (omega G) ≫ (Scheme.Modules.pullback f').map (omegaBase h) ≫
      omegaBase h' = omegaBase h'' := by
    refine pullback_hom_ext (sec_hom η[G]) fun W a => ?_
    have k₁ := le_of_sq (unitSec_comp h) (le_refl (unitSec G ⁻¹ᵁ W)) le_rfl
    have k₂ := le_of_sq (unitSec_comp h') k₁ le_rfl
    refine (k le_rfl le_rfl le_rfl (dUnit G le_rfl a)).trans ?_
    rw [omegaBase_dUnit h le_rfl le_rfl k₁ le_rfl, omegaBase_dUnit h' k₁ le_rfl k₂ le_rfl]
    exact (congrArg _ (appLE_appLE rfl _ _ le_rfl a)).trans (omegaBase_dUnit h'' le_rfl le_rfl k₂ le_rfl a).symm
  rw [← this, k hV hW]

variable {k : Type} [CommRing k] {C : Scheme.{0}} {G : Over C} [GrpObj G] {x : Sp k ⟶ C} {B : Over (Sp k)} [GrpObj B]
  {ψ : B.left ⟶ G.left}

end Tangent

section Pairing

open GlobalTheory.Published.AbelianDeRham (bcMor)

end Pairing

open GlobalTheory.DeRhamSheaf (onAff)
open GlobalTheory.Published.AbelianDeRham (bcMor)
open GlobalTheory.DualPull (theta dualApp_theta)


end GlobalTheory.BadPt.Fibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfAgreeOnClosedFibreDualNumbers
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKS

theorem preimage_eq_of_agree_closedFibre : ∀ (k : Type) [Field k] (X B : Scheme.{0}) (h : B ⟶ Sp (DualNumber k)) (π₁ π₂ : B ⟶ X), (∀ (Z : Scheme.{0}) (x : Z ⟶ B) (y : Z ⟶ Sp k), x ≫ h = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ W : X.Opens, π₁ ⁻¹ᵁ W = π₂ ⁻¹ᵁ W := by
  intro k _ X B h π₁ π₂ hyp W
  have hpt : ∀ b : B, π₁ b = π₂ b := by
    intro b
    set x := B.fromSpecResidueField b
    set φ := Spec.preimage (x ≫ h)
    have hφ : Spec.map φ = x ≫ h := Spec.map_preimage _
    have hinr : ∀ c : k, φ.hom (TrivSqZeroExt.inr c) = 0 := by
      intro c
      have : φ.hom (TrivSqZeroExt.inr c) * φ.hom (TrivSqZeroExt.inr c) = 0 := by
        rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]
      exact mul_self_eq_zero.mp this
    let ψ : k →+* B.residueField b := φ.hom.comp (TrivSqZeroExt.inlHom k k)
    have hψ : ψ.comp (TrivSqZeroExt.fstHom k k k).toRingHom = φ.hom := by
      refine RingHom.ext fun z => ?_
      conv_rhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z]
      rw [map_add (f := _), hinr, add_zero]
      rfl
    have hx : x ≫ h = Spec.map (CommRingCat.ofHom ψ) ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := by
      rw [← hφ, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
      rfl
    have e := hyp _ x _ hx
    obtain ⟨s⟩ : Nonempty (Spec (B.residueField b)) := inferInstance
    have h1 : (x ≫ π₁) s = (x ≫ π₂) s := by rw [e]
    simpa [x] using h1
  apply TopologicalSpace.Opens.ext
  ext b
  change π₁ b ∈ W ↔ π₂ b ∈ W
  rw [hpt b]

end GlobalTheory.LogKS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalDivisorDegreeZeroFiniteFieldCurve
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PrincDegZero

theorem log_card_eq (κ : Type) [Field κ] [Finite κ] (V : Type) [AddCommGroup V] [Module κ V] :
    Real.log (Nat.card V) = Module.finrank κ V * Real.log (Nat.card κ) := by
  by_cases h : Module.Finite κ V
  · have : Finite V := Module.finite_of_finite κ
    rw [Module.natCard_eq_pow_finrank (K := κ)]
    push_cast
    rw [Real.log_pow]
  · rw [Module.finrank_of_not_finite h]
    have : Infinite V := by
      by_contra h'
      have := not_infinite_iff_finite.1 h'
      exact h (Module.Finite.of_finite)
    simp [Nat.card_eq_zero_of_infinite]

theorem log_card_residueField {κ : Type} [Field κ] [Finite κ] {Y : Scheme.{0}} [IsIntegral Y] [Algebra κ Γ(Y, ⊤)]
    [LocallyOfFiniteType (strHom κ (X := Y))] (hd : topologicalKrullDim Y = (0 + 1 : ℕ)) {z : Y}
    (hz : Order.coheight z = 1) :
    Real.log (Nat.card (Y.residueField z)) =
      (interNumRed κ (⟨closure {z}, isClosed_closure⟩ : Closeds Y) (Fin.elim0 : Fin 0 → LB Y) : ℝ) *
        Real.log (Nat.card κ) := by
  have hdim := VdmRec.CutSec.dim_closure_of_coheight_field (strHom κ Y) hd hz
  obtain ⟨W, j, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  have hrange : Set.range j = closure {j (genericPoint W)} := by
    rw [← Set.image_singleton, j.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]
  letI := algebraΓAlong κ j
  have hW : topologicalKrullDim W = (0 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).symm.trans hdim
  rw [InterModel.interNumRed_eq_interNumOn _ j _ hrange,
    interNumOn_eq_interNum_pull (appTop_algebraMap_along κ j) (fun i => i.elim0), interNum_of_isEmpty]
  have hu (w : W) : w = genericPoint W := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds W) ≤ 0
      from hW.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ W, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec W)
  have hZ : ({genericPoint W} : Set W) = Set.univ := Set.eq_univ_of_forall hu
  have hc : IsClosed ({genericPoint W} : Set W) := hZ ▸ isClosed_univ
  have := isClosed_singleton_iff_isClosedImmersion.1 hc
  have : Surjective (W.fromSpecResidueField (genericPoint W)) :=
    ⟨fun w => ⟨IsLocalRing.closedPoint _, (hu _).trans (hu w).symm⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (W.fromSpecResidueField (genericPoint W))
  have : IsAffine W := .of_isIso (inv (W.fromSpecResidueField (genericPoint W)))
  have : IsIso (W.fromSpecResidueField (genericPoint W)).appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  have b₁ : Function.Bijective (j.residueFieldMap (genericPoint W)) := by
    refine ⟨RingHom.injective _, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := W.residue_surjective _ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective _ a
    exact ⟨Y.residue _ b, by rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩
  have b₂ : Function.Bijective ((W.fromSpecResidueField (genericPoint W)).appTop ≫
      (Scheme.ΓSpecIso (W.residueField (genericPoint W))).hom) := ConcreteCategory.bijective_of_isIso _
  have e : Γ(W, ⊤) ≃ Y.residueField (j (genericPoint W)) :=
    (Equiv.ofBijective _ b₂).trans (Equiv.ofBijective _ b₁).symm
  rw [← Nat.card_congr e, chi_structureModule_of_isAffine, log_card_eq κ]
  push_cast
  ring

end GlobalTheory.PrincDegZero

namespace GlobalTheory.PrincDegZero

theorem finsum_ord_mul_log_card_eq_zero : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (1 : ℕ) → ∀ (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Y, ⊤)] (f : Y.functionField), f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = 0 := by
  intro k _ Y _ _ q hA hd l _ _ f hf
  have : Module.Finite ℤ k := hA.finite
  have : AlgebraicGeometry.IsNoetherian Y := hA.isNoetherian
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hpr, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hA.isProjOver
  have hp : IsProjOver (strHom (ZMod l) (X := Y)) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l)) = q ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod l) (X := Y)) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨this, H, hH⟩
  have : IsProper (strHom (ZMod l) (X := Y)) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have hd' : topologicalKrullDim Y = (0 + 1 : ℕ) := hd
  let r : (LB.triv Y).ι → Y.functionFieldˣ := fun _ => Units.mk0 f hf
  have hr : IsRatSec (LB.triv Y) r := fun _ _ h => by simp [r]
  have hM := LB.isLB_triv Y
  have key := GlobalTheory.ratSec_cycle_formula (ZMod l) Y hp 0 hd.le (LB.triv Y) hM Fin.elim0 (fun i => i.elim0) r hr
  rw [interNum_eq_zero_of_cls_eq_zero (ZMod l) _ (isLB_cons hM fun i => i.elim0) 0 (cls_triv _)] at key
  have hm (z : Y) : (divOfRatSec hM hr).mult z = Scheme.ord f z :=
    ((presents_divOfRatSec hM hr).isEqn PUnit.unit z trivial).mult_eq
  have hfin : Function.HasFiniteSupport fun w => (divOfRatSec hM hr).mult w *
      interNumRed (ZMod l) (⟨closure {w}, isClosed_closure⟩ : Closeds _) (Fin.elim0 : Fin 0 → LB Y) :=
    (CartierDiv.finite_support_mult _).subset (Function.support_mul_subset_left _ _)
  have em := (AddMonoidHom.mulRight (Real.log (Nat.card (ZMod l)))).comp (Int.castAddHom ℝ) |>.map_finsum hfin
  rw [← key] at em
  simp only [map_zero] at em
  refine (finsum_congr fun z => ?_).trans em.symm
  change (Scheme.ord f z : ℝ) * _ = (((divOfRatSec hM hr).mult z * _ : ℤ) : ℝ) * _
  rw [hm]
  by_cases hz : Scheme.ord f z = 0
  · simp [hz]
  have hc : Order.coheight z = 1 := by
    by_contra h
    exact hz (Scheme.ord_eq_zero_of_coheight_neq_one h f)
  rw [Int.cast_mul, mul_assoc, log_card_residueField (κ := ZMod l) hd' hc]

end GlobalTheory.PrincDegZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEqTauFromSignRelationFourTorsionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_eq_tau_from_sign_relation_four_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (O : Type) [CommRing O] [StarRing O] [Module O D.X] (o : D.OAct O) (w : O), w + star w = 1 → ∀ u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w), Normd u → ∀ gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]), Normd gam → ∀ p q r : QkPt D F 4, q.y = w • p.y → r.y = (1 + w) • p.y → GtAct o w p.g q.g → GtAct o (1 + w) p.g r.g → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ s s' s'' : ((TF (R := R) F).left.presheaf.stalk z)ˣ, s * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (p.g.s p.y) (𝟙 _) z J ^ 2 * val gam p.g.b.left z J → s' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (q.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (q.g.s q.y) (𝟙 _) z J ^ 2 * val gam q.g.b.left z J → s'' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (r.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (r.g.s r.y) (𝟙 _) z J ^ 2 * val gam r.g.b.left z J → s'' = s ^ 2 * s' → @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) * val u (cP D (TF (R := R) F) p.y).left z J = @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J := by
  first | exact @GlobalTheory.PsiSignRel.sign_rel | exact GlobalTheory.PsiSignRel.sign_rel | (intros; apply GlobalTheory.PsiSignRel.sign_rel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartRestrictionIsWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatMod

theorem isWt_fourierTerm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (W : Y.H.left.Opens), (∃ V : Q.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → W ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α W (rsT (τ.f fun _ => j) W) := by
  intro R _ _ Q Ω _ _ _ oa Y k α σ τ hT j W _ hW
  exact GlobalTheory.Heat.TermWt.isWt_term Y k α σ τ hT (fun _ => j) W fun _ hx => Set.mem_iInter.2 fun _ => hW hx

end GlobalTheory.HeatMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudShiftUnitIdentityFractionFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaudShift_unitIdentity_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Q.TauBimult → ∀ (k : ℕ) (mu α : Q.X) (xp : 𝟙_ (Over (Sp R)) ⟶ Y.H) (A₀ B₀ P₀ : R) (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1)) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left ≫ Y.q.left] ![1, -1])), xp ≫ Y.q = Q.c mu → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z A₀ * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 Z) z J).val = cst (g ≫ jK R) z B₀ * (val (Q.tau mu α) g z J).val) → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi mu) g z J).val = cst (g ≫ jK R) z P₀ * (val ψ₀ (g ≫ jK R) z J).val) → (∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ xp⁻¹))).s mu) (𝟙 _) z J = 1) → ∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) k mu α) → ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (pp : Over.mk (g ≫ jK R) ⟶ DegPre.BF Q (FractionRing R)) (yp : Over.mk (g ≫ jK R) ⟶ Y.H), (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g → pp ≫ DegPre.prB Q (FractionRing R) = yp ≫ Y.q → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z B₀ * (val u (show Z ⟶ _ from pp.left) z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 Z) z J).val * ((val e (show Z ⟶ Y.H.left from (yp * (toUnit _ ≫ xp)).left) z J) ^ k).val = cst (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 Z) z J).val := by
  first | exact @GlobalTheory.ShiftUnit.shift_unit_identity | exact GlobalTheory.ShiftUnit.shift_unit_identity | (intros; apply GlobalTheory.ShiftUnit.shift_unit_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondOrderSymbolBracketRescaleByUnitPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem bracket_symbol_rescale_twist : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (δ₀ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Λ : Matrix (Fin n) (Fin n) (FractionRing Ω)) (q b c : FractionRing Ω) (k : ℕ), q ≠ 0 → (k : FractionRing Ω) * (q ^ k * b) * ((q ^ k * b) * δ₀ (q ^ k * c) - (q ^ k * c) * δ₀ (q ^ k * b)) - ∑ a, ∑ e, Λ a e * δL a (q ^ k * b) * ((q ^ k * b) * δL e (q ^ k * c) - (q ^ k * c) * δL e (q ^ k * b)) = q ^ (3 * k) * ((k : FractionRing Ω) * b * (b * (δ₀ c - ∑ a, ∑ e, Λ a e * δL a q / q * δL e c) - c * (δ₀ b - ∑ a, ∑ e, Λ a e * δL a q / q * δL e b)) - ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b)) := by
  intro Ω _ _ n δ₀ δL Λ q b c k hq
  have hpow : ∀ (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (x : FractionRing Ω),
      d (q ^ k * x) = q ^ k * (d x + (k : FractionRing Ω) * x * (d q / q)) := by
    intro d x
    rw [Derivation.leibniz, Derivation.leibniz_pow]
    cases k with
    | zero => simp
    | succ k =>
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      field_simp
      ring
  have hbr : ∀ d : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      (q ^ k * b) * d (q ^ k * c) - (q ^ k * c) * d (q ^ k * b)
        = q ^ k * q ^ k * (b * d c - c * d b) := by
    intro d
    rw [hpow d b, hpow d c]
    ring
  have h3 : q ^ (3 * k) = q ^ k * q ^ k * q ^ k := by ring
  simp only [hbr]
  simp only [hpow _ b]
  have hs : ∑ a, ∑ e, Λ a e * (q ^ k * (δL a b + (k : FractionRing Ω) * b * (δL a q / q))) *
        (q ^ k * q ^ k * (b * δL e c - c * δL e b))
      = q ^ k * q ^ k * q ^ k * ((k : FractionRing Ω) * b *
          (b * (∑ a, ∑ e, Λ a e * δL a q / q * δL e c)
            - c * (∑ a, ∑ e, Λ a e * δL a q / q * δL e b))
          + ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hs, h3]
  ring

end GlobalTheory.Heat
end

