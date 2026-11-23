module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverTargetOfIsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExistsIffTopExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfIsPartOfBasisBalFormsOfMem
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

theorem eq_zero_of_linearIndependent_int_rat {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (q : ι → ℚ) (hq : ∀ y, ∑ i, q i * (f i y : ℚ) = 0) : q = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  have hb' : ∀ i, ∃ r : ℤ, (r : ℚ) = ((b : ℤ) : ℚ) * q i := fun i => by
    obtain ⟨r, hr⟩ := hb i
    exact ⟨r, by simpa [Algebra.smul_def] using hr⟩
  choose n hn using hb'
  have h0 : n = 0 := by
    rw [Fintype.linearIndependent_iff] at hf
    funext i
    refine hf n ?_ i
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have : ((∑ i, n i * f i y : ℤ) : ℚ) = ((b : ℤ) : ℚ) * ∑ i, q i * (f i y : ℚ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hn i]; ring
    rw [hq y, mul_zero] at this
    exact_mod_cast this
  funext i
  have hbne : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have h := hn i
  rw [h0] at h
  simp only [Pi.zero_apply, Int.cast_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hbne

theorem eq_zero_of_linearIndependent_int {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (k : Type) [Field k] [CharZero k] (a : ι → k)
    (ha : ∀ y, ∑ i, a i * (f i y : k) = 0) : a = 0 := by
  classical
  let B := Module.Basis.ofVectorSpace ℚ k
  have key : ∀ j, (fun i => B.coord j (a i)) = 0 := fun j =>
    eq_zero_of_linearIndependent_int_rat hf _ fun y => by
      have h := congrArg (B.coord j) (ha y)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  funext i
  apply B.repr.injective
  ext j
  have := congrFun (key j) i
  simpa [Module.Basis.coord_apply] using this

end GlobalTheory.PolFan

namespace GlobalTheory.PolFan

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantNormalProjectiveCompactification
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

noncomputable section
namespace GlobalTheory.EqModel

theorem isProjOver_pi_const {R : Type} [CommRing R] (κ : Type) [Finite κ] (A : Over (Sp R))
    (h : IsProjOver A.hom) : IsProjOver (∏ᶜ fun _ : κ => A).hom := by
  let n := Nat.card κ
  let e : κ ≃ Fin n := Finite.equivFin κ
  let I₁ : (∏ᶜ fun _ : κ => A) ≅ ∏ᶜ fun _ : Fin n => A := (Pi.reindex e.symm (fun _ : κ => A)).symm
  let I₂ : (∏ᶜ fun _ : Fin n => A) ≅ ReciprocityTheory.ChartRestriction.G.Out.powObj A n :=
    (limit.isLimit _).conePointUniqueUpToIso (ReciprocityTheory.ChartRestriction.G.Out.powIsLimit A n)
  have : IsIso (I₁ ≪≫ I₂).hom.left := ((Over.forget _).mapIso (I₁ ≪≫ I₂)).isIso_hom
  have hp := Models.FamInh.isProjOver_powObj A h n
  have e' := ProjSpace.isProjOver_comp_of_isClosedImmersion (I₁ ≪≫ I₂).hom.left hp
  rwa [Over.w] at e'

theorem isOpenImmersion_toNormalization {V P X : Scheme.{0}} (c : V ⟶ P) (p : P ⟶ X) [IsSeparated p]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact c] [QuasiSeparated c] (h : c ≫ p = j) :
    IsOpenImmersion c.toNormalization := by
  first
  | (rename_i h_5 h_7 h_8 h_9; revert V P X c p h_5 j h_7 h_8 h_9 h; exact @_root_.GlobalTheory.NormalizationOpenImmersion.main)
  | exact @_root_.GlobalTheory.NormalizationOpenImmersion.main
  | exact _root_.GlobalTheory.NormalizationOpenImmersion.main
  | (apply _root_.GlobalTheory.NormalizationOpenImmersion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormalizationOpenImmersion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormalizationOpenImmersion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormalizationOpenImmersion.main ..)

theorem isQProjOver_of_isProjOver' {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsQProjOver f := by
  obtain ⟨N, i, _, e⟩ := h
  exact ⟨N, i, inferInstance, inferInstance, e⟩

theorem exists_projective_quotient {F : Type} [Field F] {X : Scheme.{0}} (s : X ⟶ Sp F) {Γ : Type}
    [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (hs : IsProjOver s) (hρ : ∀ g, (ρ g).asIso.hom ≫ s = s) :
    ∃ (W : Scheme.{0}) (q : X ⟶ W) (sW : W ⟶ Sp F), IsAffineQuotient ρ q ∧ q ≫ sW = s ∧
      IsProjOver sW ∧ IsFinite q ∧ Surjective q := by
  have := OrbitsInAffineOpens.of_isQProjOver (isQProjOver_of_isProjOver' hs) ρ
  obtain ⟨W, q, hq⟩ := QuotientGluing.exists_isAffineQuotient ρ
  have hqs := hq.comp_desc s hρ
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hs).1
  have : IsProper (q ≫ hq.desc s hρ) := by rw [hqs]; infer_instance
  have : LocallyOfFiniteType (q ≫ hq.desc s hρ) := by rw [hqs]; infer_instance
  have : IsProper (hq.desc s hρ) := hq.isProper _
  obtain ⟨L, hL⟩ := GaloisQuotient.exists_isAmpleLB_of_isAffineQuotient hq
    (isQProjOver_of_isProjOver' hs)
  exact ⟨W, q, hq.desc s hρ, hq, hqs, hL.isProjOver _, hq.isFinite (hq.desc s hρ), hq.surjective⟩

theorem exists_equivariant_model : ∀ (F : Type) [Field F] [NumberField F] (X V : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (j : V ⟶ X) [IsOpenImmersion j] (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut V), IsProjOver sX → Nonempty V → GlobalTheory.IsNormalScheme V → (∀ γ, (ρ γ).asIso.hom ≫ j ≫ sX = j ≫ sX) → ∃ (X' W : Scheme.{0}) (φ : X' ⟶ X) (ℓ : V ⟶ X') (ρ' : Γ →* Aut X') (q : X' ⟶ W) (sW : W ⟶ Sp F) (_ : IsIntegral X'), GlobalTheory.IsNormalScheme X' ∧ IsProjOver (φ ≫ sX) ∧ IsOpenImmersion ℓ ∧ ℓ ≫ φ = j ∧ (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) ∧ IsAffineQuotient ρ' q ∧ q ≫ sW = φ ≫ sX ∧ IsProjOver sW ∧ IsIntegral W ∧ IsFinite q ∧ Surjective q := by
  intro F _ _ X V _ sX j _ Γ _ _ ρ hX hne hN hρ
  classical
  let A : Over (Sp F) := Over.mk sX
  let P : Over (Sp F) := ∏ᶜ fun _ : Γ => A
  let B : Over (Sp F) := Over.mk (j ≫ sX)
  let c : B ⟶ P := Pi.lift fun γ => Over.homMk ((ρ γ).asIso.hom ≫ j) (by simpa [A, B] using hρ γ)
  have hcπ (γ : Γ) : c.left ≫ (Pi.π (fun _ : Γ => A) γ).left = (ρ γ).asIso.hom ≫ j := by
    rw [← Over.comp_left, Pi.lift_comp_π]; rfl

  let σ₀ (g : Γ) : P ⟶ P := Pi.lift fun γ => Pi.π (fun _ : Γ => A) (γ * g)
  have hσπ (g γ : Γ) : σ₀ g ≫ Pi.π (fun _ : Γ => A) γ = Pi.π (fun _ : Γ => A) (γ * g) :=
    Pi.lift_comp_π _ _
  have hσ (g h : Γ) : σ₀ g ≫ σ₀ h = σ₀ (h * g) :=
    Pi.hom_ext _ _ fun γ => by rw [Category.assoc, hσπ, hσπ, hσπ, mul_assoc]
  have hσ1 : σ₀ 1 = 𝟙 P := Pi.hom_ext _ _ fun γ => by rw [hσπ, mul_one, Category.id_comp]
  let σI (g : Γ) : P.left ≅ P.left :=
    { hom := (σ₀ g).left, inv := (σ₀ g⁻¹).left,
      hom_inv_id := by rw [← Over.comp_left, hσ, inv_mul_cancel, hσ1]; rfl,
      inv_hom_id := by rw [← Over.comp_left, hσ, mul_inv_cancel, hσ1]; rfl }
  let σ : Γ →* Aut P.left := MonoidHom.mk' (fun g => Aut.of (σI g)) fun g h => by
    apply Aut.ext
    apply Iso.ext
    change (σ₀ (g * h)).left = (σ₀ h).left ≫ (σ₀ g).left
    rw [← Over.comp_left, hσ]
  have hσP (g : Γ) : (σ g).asIso.hom ≫ P.hom = P.hom := Over.w (σ₀ g)
  have hρmul (g γ : Γ) : (ρ (γ * g)).asIso.hom = (ρ g).asIso.hom ≫ (ρ γ).asIso.hom := by rw [map_mul]; rfl
  have H (g : Γ) : (ρ g).asIso.hom ≫ c.left = c.left ≫ (σ g).asIso.hom := by
    have e : (Over.homMk (ρ g).asIso.hom (by simpa [B] using hρ g) : B ⟶ B) ≫ c = c ≫ σ₀ g :=
      Pi.hom_ext _ _ fun γ => by
        rw [Category.assoc, Category.assoc, hσπ]
        ext1
        simp only [Over.comp_left, hcπ, Over.homMk_left, hρmul, Category.assoc]
    exact congrArg CommaMorphism.left e

  have : IsProper sX := ((isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hX).1
  have hP : IsProjOver P.hom := isProjOver_pi_const Γ A hX
  have : IsProper P.hom := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hP).1
  have hcP : c.left ≫ P.hom = j ≫ sX := Over.w c
  have hc1 : c.left ≫ (Pi.π (fun _ : Γ => A) 1).left = j := by rw [hcπ, map_one]; rfl
  have : IsSeparated (c.left ≫ P.hom) := by rw [hcP]; infer_instance
  have : QuasiSeparated c.left := .of_comp c.left P.hom
  have : IsSeparated (Pi.π (fun _ : Γ => A) 1).left := by
    have : IsSeparated ((Pi.π (fun _ : Γ => A) 1).left ≫ sX) := Over.w (Pi.π (fun _ : Γ => A) 1) ▸ inferInstance
    exact .of_comp _ sX
  have : IsIntegral V := isIntegral_of_isOpenImmersion j
  have : IsIntegral B.left := ‹IsIntegral V›
  have : GlobalTheory.IsNormalScheme B.left := hN
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (j ≫ sX)
  have : CompactSpace V := ⟨by
    rw [j.isOpenEmbedding.isInducing.isCompact_iff, Set.image_univ]
    exact NoetherianSpace.isCompact _⟩
  have : IsNoetherian V := {}
  have : QuasiCompact (c.left ≫ (Pi.π (fun _ : Γ => A) 1).left) := by
    rw [hc1]
    exact quasiCompact_of_noetherianSpace_source j
  have : QuasiCompact c.left := .of_comp c.left (Pi.π (fun _ : Γ => A) 1).left
  have : LocallyOfFiniteType (c.left ≫ P.hom) := by rw [hcP]; infer_instance
  have : LocallyOfFiniteType c.left := locallyOfFiniteType_of_comp c.left P.hom

  have hfin : IsFinite c.left.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType c.left P.hom fun x _ =>
      charZero_of_injective_ringHom
        ((Scheme.ΓSpecIso (.of F)).inv ≫ (j ≫ sX).appTop ≫ V.Γevaluation x).hom.injective
  let φ : c.left.normalization ⟶ X := c.left.fromNormalization ≫ (Pi.π (fun _ : Γ => A) 1).left
  have hφ : φ ≫ sX = c.left.fromNormalization ≫ P.hom := by
    simp only [φ, Category.assoc]
    congr 1
    exact Over.w (Pi.π (fun _ : Γ => A) 1)
  have hproj : IsProjOver (φ ≫ sX) := hφ ▸ isProjOver_comp_of_isFinite _ hP
  have hnorm : GlobalTheory.IsNormalScheme c.left.normalization :=
    IsNormalScheme.normalization_of_isIntegral c.left
  let ρ' := normalizationAction c.left ρ σ H
  have hρ' (g : Γ) : (ρ' g).asIso.hom ≫ φ ≫ sX = φ ≫ sX := by
    rw [hφ, normalizationAction_fromNormalization_assoc, hσP]
  obtain ⟨W, q, sW, hq, hqs, hW, hqf, hqs'⟩ := exists_projective_quotient (φ ≫ sX) ρ' hproj hρ'
  refine ⟨c.left.normalization, W, φ, c.left.toNormalization, ρ', q, sW, inferInstance, hnorm, hproj,
    isOpenImmersion_toNormalization c.left (Pi.π (fun _ : Γ => A) 1).left j hc1, ?_,
    fun g => (toNormalization_normalizationAction c.left ρ σ H g).symm, hq, hqs, hW, hq.isIntegral,
    hqf, hqs'⟩
  simp only [φ, Scheme.Hom.toNormalization_fromNormalization_assoc, hc1]

end GlobalTheory.EqModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHodgeWt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeLin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def offCM (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) : ℤ :=
  if τ (H.rt : E) = H.rt0 then 0 else if conjEmb τ (H.rt : E) = H.rt0 then 1 else 0

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exOf_hodgeWt (Dw : Datum H) :
    GlobalTheory.AllWt.exOf Dw (hodgeWt Dw) 0 = fun ix => ix.elim 0 fun x => offCM H x.1 := by
  funext ix
  rcases ix with _ | ⟨τ, i⟩
  · rfl
  · simp only [GlobalTheory.AllWt.exOf, exZ, GlobalTheory.AllWt.wtOf, Option.elim, offCM, hodgeWt, CompHt.barWt]
    by_cases h : τ (H.rt : E) = H.rt0
    · simp only [dif_pos h, if_pos h]
      split_ifs <;> omega
    · have hm : Dw.mult τ = Dw.q := by simp [Datum.mult, h]
      have hi : (i : ℕ) < Dw.q := lt_of_lt_of_eq i.2 hm
      simp only [dif_neg h, if_neg h]
      by_cases h' : conjEmb τ (H.rt : E) = H.rt0
      · simp only [dif_pos h', if_pos h', dif_pos hi]
        split_ifs <;> omega
      · simp only [dif_neg h', if_neg h']

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def DetEqns (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)]
    (φ₀ : c.F →+* (X₀ TF.Y Z).functionField)
    (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from
      (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι))
    (a : (E →+* ℂ) → ℤ) (D : CartierDiv (X₀ TF.Y Z)) : Prop :=
  ∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x)
    (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from
      (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField)
    (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ),
    (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧
    (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧
    (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from
      (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)
      (fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k)
      (A τ i) (f₀.v τ i)) ∧
    D.IsEqn x (∏ τ, d τ ^ (-a τ))

section Eqv

def EqvLin {X Y : Scheme.{0}} (t : SAB H Y) (p : X ⟶ Y) {Γ : Type} [Group Γ] (ρ' : Γ →* Aut X) (G' : Over X)
    [GrpObj G'] (ψ : G'.left ⟶ t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)) : Prop :=
  IsGrpPullback G' t.G p ψ ∧ (∀ a, (act'.act a).left ≫ ψ = ψ ≫ (t.act.act a).left) ∧
    (∀ γ, IsGrpPullback G' G' (ρ' γ).asIso.hom (m γ)) ∧ (∀ γ a, (act'.act a).left ≫ m γ = m γ ≫ (act'.act a).left) ∧
    (∀ γ₁ γ₂, m (γ₁ * γ₂) = m γ₂ ≫ m γ₁) ∧
    ∀ γ (x : X), X.fromSpecResidueField x ≫ (ρ' γ).asIso.hom = X.fromSpecResidueField x →
      ∀ (T : Scheme.{0}) (w : T ⟶ G'.left) (v : T ⟶ Spec (X.residueField x)),
        w ≫ G'.hom = v ≫ X.fromSpecResidueField x → w ≫ m γ = w

end Eqv

end GlobalTheory.HodgeLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAtOfOneMeasure
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.CovTop.MeasRd

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem sgAt_mk_eq {K : Type} [Field K] (σ₀ σ : K →+* ℂ) :
    sgAt σ₀ (InfinitePlace.mk σ) = σ ∨ sgAt σ₀ (InfinitePlace.mk σ) = (starRingEnd ℂ).comp σ := by
  have hc : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
    RingHom.ext fun a => ComplexEmbedding.conjugate_coe_eq σ a
  unfold sgAt
  split_ifs with h
  · rcases InfinitePlace.mk_eq_iff.1 h with h1 | h1
    · exact Or.inl h1.symm
    · right; rw [← h1, hc]
  · rcases InfinitePlace.embedding_mk_eq σ with h1 | h1
    · exact Or.inl h1
    · right; rw [h1, hc]

theorem phiC_congr {T : CoreJ D} {j : ℕ} {σ₁ σ₂ : T.Q.c.F →+* ℂ} (e : σ₁ = σ₂) {W : Formalism.BasicNotions.TH.HSp D}
    (h₁ : T.V j σ₁ = W) (h₂ : T.V j σ₂ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T h₁ a f = phiC T h₂ a f := by
  subst e; rfl

end GlobalTheory.CovTop.MeasRd

namespace GlobalTheory.CovTop.MeasRd


end GlobalTheory.CovTop.MeasRd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactRatioOfFundamentalDomain
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExactRatioProof

open scoped InnerProductSpace ComplexConjugate

theorem L1 : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := _root_.GlobalTheory.DimProdLab.prod_dims

theorem K2aux (D : D7) (T : CoreJ D) (h : LawsJ T) (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ) (hs : GoodEmb T.Q.c s)
    (f : FDSec (T.U ((i : ℕ) + 1) s).X) (W : HSp D) (hV : T.V ((i : ℕ) + 1) s = W) :
    eLpNorm' (fun q : AutQ W => ‖(hV ▸ ((lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) : ℂ) •
      adel (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s)
        (muPin (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (T.mu ((i : ℕ) + 1) s) (T.cE ((i : ℕ) + 1) s)) f) :
          GA D W → ℂ) q.out‖) 2 (muQ1 W) =
      ENNReal.ofReal (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) *
        petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s))
          (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f := by
  subst hV
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hmu := h.muUnit _ hj s hs
  have hcu := h.cUnit _ hj s hs
  set c := lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) with hcdef
  have hc0 : 0 < c := lieFacZ_pos _ _
  unfold petE
  rw [← Real.enorm_eq_ofReal hc0.le, ← eLpNorm'_const_smul c (by norm_num)]
  refine eLpNorm'_congr_norm_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc0, adel_muPin]
  rw [hcu, hmu.2.1]
  simp only [abs_one, one_mul, abs_norm, abs_of_nonneg (ptN_nonneg _ _ _)]
  unfold ptN
  rw [pnorm_eq_of_unit _ _ _ _ (hmu.2.2.2 _)]

theorem K2 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ), GoodEmb T.Q.c s → ∀ (hV : T.V ((i : ℕ) + 1) s = Wc D i) (f : FDSec (T.U ((i : ℕ) + 1) s).X), eLpNorm' (fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) 2 (muQ1 (Wc D i)) = ENNReal.ofReal (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) * petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s)) (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f :=
  fun D T h i s hs hV f => K2aux D T h i s hs f (Wc D i) hV

theorem K3 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ), GoodEmb T.Q.c s → ∀ f ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.scalarForms T i s, petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s)) (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f ≠ ⊤ := by
  intro D T h i s hs f hf
  obtain ⟨th, hr, -, hdu⟩ := h.dictU _ ⟨Nat.le_add_left _ _, i.2⟩ s hs
  exact petE_ne_top _ _ _ prob_le_one hdu.2.2.2.1 hf

end GlobalTheory.ExactRatioProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineHolFrames
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.ShFam.HolFrames

theorem exists_affine_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) {T : Scheme.{0}} (io : T ⟶ gen Y) (y : T) :
    ∃ (W : T.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(T, W))
      (_ : EigFrame Y φ (((show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io) ≫ genι Y)),
      y ∈ W ∧ ((show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io) ≫ genStr Y = spMap φ := by
  obtain ⟨U, hU, φ, f, hy, hφ, -⟩ := GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H D l Xo c O β Y (io y)
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (a := y) (u := (io ⁻¹ᵁ U : T.Opens)) hy (io ⁻¹ᵁ U).2
  have hW : IsAffineOpen W := hW
  have e : (show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io =
      spMap (io.appLE U W hWU).hom ≫ (show Sp Γ(gen Y, U) ⟶ gen Y from hU.fromSpec) :=
    (IsAffineOpen.SpecMap_appLE_fromSpec io hU hW hWU).symm
  obtain ⟨g, -⟩ := exists_bc f (io.appLE U W hWU).hom (φ' := (io.appLE U W hWU).hom.comp φ)
    (x' := ((show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io) ≫ genι Y) rfl (by rw [e, Category.assoc])
  refine ⟨W, hW, _, g, hyW, ?_⟩
  rw [e, Category.assoc, spMap_comp₂]
  exact congrArg _ hφ


open GlobalTheory.Points GlobalTheory.ShFam.EigLoc in
theorem exists_affine_holFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (e : c.F →+* ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsOpenImmersion io → io ≫ genStr Y = B.str → ∃ (W : B.X → B.X.Opens) (hW : ∀ y, IsAffineOpen (W y)) (φ : ∀ y, c.F →+* Γ(B.X, W y)) (fr : ∀ y, EigFrame Y (φ y) (((show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) ≫ io) ≫ genι Y)) (a : B.X → GlobalTheory.CxPts B.str e → CxFr Y e), (∀ y, y ∈ W y) ∧ (∀ y, ((show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) ≫ io) ≫ genStr Y = spMap (φ y)) ∧ (∀ y p, (a y p).1.1 = p.1 ≫ io) ∧ (∀ y p (h : p ∈ GlobalTheory.CxPts.ptsIn B.str e (W y)) ρ i, (a y p).2.v ρ i = spMap (Chart.dualMapR (GlobalTheory.CxPts.evHom h)) ≫ (fr y).v ρ i) ∧ ∀ y (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (A : Set V) (x : V → GlobalTheory.CxPts B.str e), IsOpen A → IsHolTo A (fun b => (x b).1) → Set.MapsTo x A (GlobalTheory.CxPts.ptsIn B.str e (W y)) → HolFam A (fun b => a y (x b)) := by
  intro E _ _ _ H D l Xo c O _ β Y e B io _ hio
  choose U hU φ fr hy hφ using fun y => exists_affine_frame Y io y
  have hov : ∀ p : GlobalTheory.CxPts B.str e, (p.1 ≫ io) ≫ genStr Y = spMap e := fun p => by
    rw [Category.assoc, hio, p.2]
  have hp : ∀ y (p : GlobalTheory.CxPts B.str e) (h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y)),
      spMap (GlobalTheory.CxPts.evHom h) ≫ (show Sp Γ(B.X, U y) ⟶ B.X from (hU y).fromSpec) = p.1 := fun y p h =>
    specMap_valMap_fromSpec (hU y) p.1 h
  have hx : ∀ y (p : GlobalTheory.CxPts B.str e) (h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y)), (p.1 ≫ io) ≫ genι Y =
      spMap (GlobalTheory.CxPts.evHom h) ≫ ((show Sp Γ(B.X, U y) ⟶ B.X from (hU y).fromSpec) ≫ io) ≫ genι Y := fun y p h => by
    rw [← hp y p h]
    simp only [Category.assoc]
  have ex : ∀ y (p : GlobalTheory.CxPts B.str e), ∃ g : EigFrame Y e ((p.1 ≫ io) ≫ genι Y),
      ∀ h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y), ∀ ρ i,
        g.v ρ i = spMap (Chart.dualMapR (GlobalTheory.CxPts.evHom h)) ≫ (fr y).v ρ i := fun y p => by
    by_cases h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y)
    · obtain ⟨g, hg⟩ := exists_bc (fr y) (GlobalTheory.CxPts.evHom h) (φ' := e) (spMap_inj (by
        rw [spMap_comp₂, ← hφ y, ← hov p, ← hp y p h]
        simp only [Category.assoc])) (hx y p h)
      exact ⟨g, fun _ => hg⟩
    · obtain ⟨g⟩ := exists_eigFrame E H D l Xo c O β Y ℂ e _ (hov p)
      exact ⟨g, fun h' => (h h').elim⟩
  choose g hg using ex
  refine ⟨U, hU, φ, fr, fun y p => ⟨⟨p.1 ≫ io, hov p⟩, g y p⟩, hy, hφ, fun _ _ => rfl, hg,
    fun y V _ _ _ A x hA hol hm => ⟨fun W f => by
      simp only [valAt'_eq_valR, valR_comp]
      exact hol (io ⁻¹ᵁ W) ((io.app W).hom f), fun ρ i => ?_⟩⟩
  exact holTan_dualMap hA ((fr y).v ρ i) (fun b hb => GlobalTheory.CxPts.evHom (hm hb)) (fun a => ⟨_,
    (hol (U y) a).2.mono fun b hb => ⟨hb, hm hb⟩, fun b hb => (GlobalTheory.CxPts.ev_eq (hm hb) a).symm⟩)
    fun b hb => hg y _ (hm hb) ρ i

end GlobalTheory.ShFam.HolFrames
end
end

