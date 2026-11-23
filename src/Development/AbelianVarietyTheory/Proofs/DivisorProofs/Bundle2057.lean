module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TangentVectorExistsUniqueUniformisingVector
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0100
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0723
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalAbelianPartValuesOfNormalForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
noncomputable section

namespace GlobalTheory.MBLow.Cl.GeoOne

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

def frW {x : KeyIn ℂ} {Y : Scheme.{0}} {M : LB Y} {φ : x.P.A.left ⟶ Y} (w : LB.Iso x.P.L (M.pull φ)) {g : ℕ}
    (u : HolUnif x.P.A x.P.L g) (j : M.ι) (z : Fin g → ℂ) : ℂ :=
  valAt' (u.ex z).left _ (w.s (fun _ => j, FrameValue.chartAt x.P.isLB (u.ex z).left)).val *
    u.fr (FrameValue.chartAt x.P.isLB (u.ex z).left) z

variable {x : KeyIn ℂ} {Y : Scheme.{0}} {M : LB Y} {φ : x.P.A.left ⟶ Y} {w : LB.Iso x.P.L (M.pull φ)} {g : ℕ}

theorem frW_eq (hM : M.IsLB) (hw : w.IsGen) (u : HolUnif x.P.A x.P.L g) (j : M.ι) (z : Fin g → ℂ) (k : x.P.L.ι)
    (hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j) (hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U k) :
    frW w u j z = valAt' (u.ex z).left _ (w.s (fun _ => j, k)).val * u.fr k z := by
  unfold frW
  have hi := le_chartAt x.P.isLB (u.ex z).left
  rw [u.fr_compat _ k z ((le_preimage_inf _ _ _).2 ⟨hi, hk⟩), ← _root_.mul_assoc]
  exact congrArg (· * u.fr k z) (GlobalTheory.Ex.Arch.FibEx.val_iso _ (pull_isLB hM φ) hw _ _ _
    ((le_preimage_wchart _ _ _ _).2 fun _ => hj) hi hk)

theorem frW_ne (u : HolUnif x.P.A x.P.L g) (j : M.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j) :
    frW w u j z ≠ 0 := by
  have hi := le_chartAt x.P.isLB (u.ex z).left
  exact mul_ne_zero (val_unit_ne_zero _ valueRules
    ((le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hj, hi⟩) _) (u.fr_ne _ _ hi)

theorem frW_compat (hw : w.IsGen) (u : HolUnif x.P.A x.P.L g) (i j : M.ι) (z : Fin g → ℂ)
    (hi : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U i) (hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j) :
    frW w u i z = valAt' ((u.ex z).left ≫ φ) (M.U i ⊓ M.U j) (M.g i j).val * frW w u j z := by
  unfold frW
  rw [← _root_.mul_assoc]
  exact congrArg (· * _) (GlobalTheory.Ex.Arch.val_iso_chart x.P.isLB hw _ i j _ hi hj (le_chartAt x.P.isLB (u.ex z).left))

theorem frW_hol (hM : M.IsLB) (hw : w.IsGen) (u : HolUnif x.P.A x.P.L g) (j : M.ι) :
    DifferentiableOn ℂ (frW w u j) {z | ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j} := by
  intro z₀ hz₀
  have hk := le_chartAt x.P.isLB (u.ex z₀).left
  have a : ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ (((M.pull φ).div x.P.L).U (fun _ => j, FrameValue.chartAt x.P.isLB (u.ex z₀).left)) :=
    (le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hz₀, hk⟩
  obtain ⟨o₂, d₂⟩ := u.hol _ (w.s (fun _ => j, FrameValue.chartAt x.P.isLB (u.ex z₀).left)).val
  have n₂ := o₂.mem_nhds a
  have d := (d₂.differentiableAt n₂).fun_mul ((u.fr_hol _).differentiableAt ((u.hol _ 0).1.mem_nhds hk))
  refine (d.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [n₂] with z hz
  obtain ⟨h₁, h₂⟩ := (le_preimage_inf _ _ _).1 hz
  exact frW_eq hM hw u j z _ ((le_preimage_wchart _ _ _ _).1 h₁ PUnit.unit) h₂

theorem valAt'_appLE_comp {X X' : Scheme.{0}} (p : Sp ℂ ⟶ X) (f : X ⟶ X') (U : X'.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (hV : ⊤ ≤ p ⁻¹ᵁ V) (s : Γ(X', U)) : valAt' p V ((f.appLE U V h).hom s) = valAt' (p ≫ f) U s := by
  show valAt' p V (resG X h ((f.app U).hom s)) = _
  rw [valAt'_res _ h _ hV, valAt'_comp]

end GlobalTheory.MBLow.Cl.GeoOne

namespace GlobalTheory.MBLow.Cl.GeoOne

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

theorem tf_hom (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] :
    (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
  simp only [TF, jFK, jK, spMap, Over.mk_hom]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem eq_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (F : DualNumber A →+* DualNumber B)
    (h1 : ∀ a, F (algebraMap A _ a) = algebraMap B _ (f a)) (h2 : F DualNumber.eps = DualNumber.eps) : F = dualMap f := by
  refine RingHom.ext fun z => ?_
  have hz : z = algebraMap A _ z.fst + algebraMap A _ z.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hz, map_add (f := _), map_mul, h1, h1, h2]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl, dualMap]

theorem eu_gen (x : KeyIn ℂ) (g : ℕ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) :
    ∀ w, IsTangent w → ∃! W, u.IsDiff W w := by
  subst hg
  exact (GlobalTheory.LamT.existsUnique_isDiff_and_linear x u).1

theorem one_left {S : Scheme.{0}} (X : Over S) [GrpObj X] : (1 : 𝟙_ (Over S) ⟶ X).left = eSec X := by
  have : (1 : 𝟙_ (Over S) ⟶ X) = η[X] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [this]; rfl

end GlobalTheory.MBLow.Cl.GeoOne

namespace GlobalTheory.MBLow.Cl

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue GlobalTheory.MBLow.Cl.GeoOne

theorem exists_ab_geo_of_nf : AllC fun {R} _ _ {D} _ {N} ν => ∀ (y : KeyIn R) (_ : y.P = D.P), HEq y.rig D.rig → (∃ th : D.P.L.Sec, HEq y.th th ∧ ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i, ν.th.f (fun _ => i) = resG _ h (th.f i)) → ∀ (x : KeyIn ℂ) (hg : x.P.g = D.P.g) (hy : y.P.g = D.P.g) (u : HolUnif x.P.A x.P.L D.P.g) (τ : Matrix (Fin D.P.g) (Fin D.P.g) ℂ) (a b : Fin D.P.g → ℂ) (c : ℂ) (W : Fin D.P.g → Fin D.P.g → ℂ), KeyPB x y ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) → NF x hg u τ a b c W → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), d.c = c ∧ ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ i, HEq (y.v (i.cast hy.symm)) (vB i)) → ∀ i (bb : TE R ℂ ⟶ D.P.A), bb.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left → ∀ W', IsD ν d W' bb ↔ W' = W i := by
  intro R _ _ _ _ D hψ hτ _ N ν y hyP hrig hth x hg hy u τ a b c W hpb hnf
  obtain ⟨P, gpos, rig, rig_gen, th, th_ne, v, basis⟩ := y
  subst hyP
  cases hrig
  obtain ⟨th', hth', hνth⟩ := hth
  cases hth'
  obtain ⟨φ, he, w, hg', F, hφ, hw, hrigm, hthm, hF1, hF2, hv⟩ := hpb
  have hnf' := hnf
  obtain ⟨hs, hp, ha, hb, hc, hΛ, hrigu, hfn, hdiff⟩ := hnf'
  obtain ⟨e, he'⟩ := LiePull.exists_pushEquiv hφ (𝟙_ (Over (Sp ℂ))) (TF (R := R) ℂ).hom
    (by rw [tf_hom]; exact (Category.id_comp _).symm)
  have hJ := ν.good
  have hex0 : u.ex 0 = 1 := by
    have := u.ex_add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have h0 : (u.ex 0).left ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A := by rw [hex0, one_left]; exact he
  have hrg0 : frW w u (ν.J (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A)) 0 = ν.rg := by
    unfold NumOf.rg vF
    rw [tf_hom]
    exact GlobalTheory.T.uniformisedFibre_frame_at_origin_eq_rigidification R D x φ he w hw hrigm _ u hrigu _ _ (le_chartAt _ _) (hJ _)
  have hrgne : ν.rg ≠ 0 := by
    rw [← hrg0]
    refine frW_ne u _ 0 ?_
    rw [h0]; exact hJ _
  have hthz : ∀ z, sF ν.th ((u.ex z).left ≫ φ) ν.J =
      c * thetaChar τ a b z * frW w u (ν.J ((u.ex z).left ≫ φ)) z := by
    intro z
    have hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ D.P.L.U (ν.J ((u.ex z).left ≫ φ)) := hJ _
    have hle : (D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) fun _ => ν.J ((u.ex z).left ≫ φ)) ≤
        D.P.L.U (ν.J ((u.ex z).left ≫ φ)) := fun q hq => Set.mem_iInter.1 hq 0
    have e0 : sF ν.th ((u.ex z).left ≫ φ) ν.J = valAt' ((u.ex z).left ≫ φ) _ (resG _ hle (th.f (ν.J ((u.ex z).left ≫ φ)))) := by
      rw [← hνth _ hle]; rfl
    rw [e0, valAt'_res _ hle _ ((le_preimage_wchart _ _ _ _).2 fun _ => by rw [Category.comp_id]; exact hj)]
    have hk := le_chartAt x.P.isLB (u.ex z).left
    have hV : ((D.P.L.pull φ).U (fun _ => ν.J ((u.ex z).left ≫ φ))) ⊓ x.P.L.U (FrameValue.chartAt x.P.isLB (u.ex z).left) ≤
        φ ⁻¹ᵁ D.P.L.U (ν.J ((u.ex z).left ≫ φ)) := inf_le_left.trans (LB.wchart_le _ _ _ PUnit.unit)
    have hpV : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((D.P.L.pull φ).U (fun _ => ν.J ((u.ex z).left ≫ φ))) ⊓
        x.P.L.U (FrameValue.chartAt x.P.isLB (u.ex z).left)) :=
      (le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hj, hk⟩
    have hm := congrArg (valAt' (u.ex z).left _) (hthm (fun _ => ν.J ((u.ex z).left ≫ φ)) _ hV)
    rw [valAt'_appLE_comp _ _ _ _ hV hpV, valAt'_mul, valAt'_res _ _ _ hpV, hfn _ z hk] at hm
    dsimp only at hm
    rw [hm]
    unfold frW
    have key : ∀ A B C E : ℂ, A = B → A * (C * E) = C * (B * E) := by intros; subst_vars; ring
    exact key _ _ _ _ rfl
  let d : AB N.toNumB D.P.g :=
    { τ := τ, a := a, b := b, c := c, symm := hs, pos := hp, ha := ha, hb := hb, hc := hc
      ex := fun z => ν.eA.symm (e (u.ex z))
      ex_add := fun z w => by simp only [u.ex_add, map_mul]
      onto := fun q => by
        obtain ⟨p, hp⟩ := e.surjective (ν.eA q)
        obtain ⟨z, rfl⟩ := u.ex_onto p
        exact ⟨z, show ν.eA.symm (e (u.ex z)) = q by rw [hp, MulEquiv.symm_apply_apply]⟩
      ker := fun z => by
        rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, u.ker, hΛ]
      fr := fun z => Units.mk0 (frW w u (ν.J ((u.ex z).left ≫ φ)) z / ν.rg) (div_ne_zero (frW_ne u _ z (hJ _)) hrgne)
      fr_zero := by
        ext
        rw [Units.val_mk0, Units.val_one, h0, hrg0, div_self hrgne]
      fr_per := fun M N z => by
        simp only [Units.val_mk0]
        have hl : u.ex (z + perV τ M N) = u.ex z := by
          rw [u.ex_add, (u.ker _).2 ((hΛ _).2 ⟨M, N, rfl⟩), _root_.mul_one]
        unfold frW
        rw [hl, frame_eq_autV_mul _ x hg u τ a b c W hnf M N _ z (le_chartAt _ _)]
        ring
      th := fun z => by
        have h1 := ν.th_eq (ν.eA.symm (e (u.ex z)))
        rw [MulEquiv.apply_symm_apply, he'] at h1
        change N.th _ * ν.rg = _ at h1
        rw [hthz z] at h1
        rw [Units.val_mk0]
        field_simp
        exact h1 }
  have hE : ∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ := fun z => by
    show (ν.eA (ν.eA.symm (e (u.ex z)))).left = _
    rw [MulEquiv.apply_symm_apply, he']
  refine ⟨d, ⟨fun i z => frW w u i z, _root_.GlobalTheory.MBLow.Cl.HolB.hol_ptB R D N ν _ d x u φ hφ hE, fun i => ?_, fun i j z h => ?_, fun z => ?_,
    fun bb hbb => ?_⟩, rfl, ?_⟩
  · simp only [hE]
    exact frW_hol D.P.isLB hw u i
  · rw [hE] at h ⊢
    exact frW_compat hw u i j z ((le_preimage_inf _ _ _).1 h).1 ((le_preimage_inf _ _ _).1 h).2
  · rw [hE]
    show (frW w u (ν.J ((u.ex z).left ≫ φ)) z / ν.rg) * ν.rg = _
    exact div_mul_cancel₀ _ hrgne
  · obtain ⟨b', hb't, hb'⟩ := _root_.GlobalTheory.MBLow.Cl.tangent_lift_of_pullback R D x φ hφ he bb hbb
    obtain ⟨W', hW', -⟩ := eu_gen x _ hg u b' hb't
    exact ⟨W', (_root_.GlobalTheory.UnifTan.isD_iff_isDiff R D N ν _ d x u φ hφ hE b' bb hb't hb' W').2 hW'⟩
  · intro vB hvB i bb hbb W'
    have hvi : v i = vB i := by
      have := eq_of_heq (hvB i)
      rwa [Fin.cast_eq_self] at this
    have hF : F = dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := eq_dualMap _ F hF1 hF2
    have hb' : (x.v (i.cast hg.symm)).left ≫ φ = bb.left := by
      rw [hv, hbb, hF, ← hvi]
      rfl
    rw [_root_.GlobalTheory.UnifTan.isD_iff_isDiff R D N ν _ d x u φ hφ hE _ bb (x.basis.1 _) hb' W']
    obtain ⟨W0, -, huniq⟩ := eu_gen x _ hg u _ (x.basis.1 (i.cast hg.symm))
    constructor
    · intro h
      exact (huniq _ h).trans (huniq _ (hdiff i)).symm
    · rintro rfl
      exact hdiff i

end GlobalTheory.MBLow.Cl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmHomGramMatrixDetNeZeroDefinite
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

theorem exists_isGram_det_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    ∃ (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
      GlobalTheory.FlatCM.IsGram X gP gQ ∧ gP.det ≠ 0 := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X
  obtain ⟨gP, gQ, h⟩ := GlobalTheory.FlatCM.GramExists.exists_isGram E H K ρ σ₁ p 0 X
  exact ⟨gP, gQ, h, (GlobalTheory.GramAt.gram_det X h).1⟩

end GlobalTheory.FlatCM.HomLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRValuationCompleteNormalLocal
section
open IsLocalRing GlobalTheory.TorRef

namespace GlobalTheory.DivBound

theorem exists_cdvr_valuation_le : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → maximalIdeal V ≠ ⊥ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (k : FractionRing V →+* FractionRing V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ (∀ v : V, k (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (j v)) ∧ ∀ x y : FractionRing V, (∃ r : V', k x = algebraMap V' (FractionRing V') r * k y) → ν x ≤ ν y := by
  intro V _ _ _ hV ν h1 h2 hm
  obtain ⟨-, -, -, h0⟩ := hV
  obtain ⟨m, hmm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hmK : algebraMap V (FractionRing V) m ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hm0
  haveI : ν.IsNontrivial := ⟨algebraMap V (FractionRing V) m, (ν.ne_zero_iff).2 hmK, (h2 m hmm).ne⟩
  haveI : IsDiscreteValuationRing ν.valuationSubring := inferInstance
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))
  haveI : CharZero ν.valuationSubring :=
    RingHom.charZero (algebraMap ν.valuationSubring (FractionRing V))
  obtain ⟨W', _, _, _, g, hW', hg, hgl⟩ := GlobalTheory.LocalCompletion.exists_cDvr_embedding ν.valuationSubring
    inferInstance inferInstance (IsDiscreteValuationRing.ringKrullDim_eq_one _) inferInstance
  obtain ⟨hdvr, hc, hz⟩ := hW'

  let i : V →+* ν.valuationSubring := (algebraMap V (FractionRing V)).codRestrict ν.valuationSubring.toSubring (fun v => h1 v)
  have hi : ∀ v : V, ((i v : ν.valuationSubring) : FractionRing V) = algebraMap V (FractionRing V) v := fun _ => rfl
  have hiinj : Function.Injective i := fun a b h =>
    IsFractionRing.injective V (FractionRing V) (by rw [← hi, ← hi, h])

  have hnu : ∀ w : ν.valuationSubring, ν (w : FractionRing V) < 1 → ¬ IsUnit w := fun w hw hu =>
    hw.ne ((Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers ν)).mp hu)
  haveI hil : IsLocalHom i := ⟨fun a ha => by
    by_contra hna
    exact hnu (i a) (by rw [hi]; exact h2 a ((mem_maximalIdeal _).2 hna)) ha⟩
  haveI := hgl
  let g' : ν.valuationSubring →+* FractionRing W' := (algebraMap W' (FractionRing W')).comp g
  have hg' : Function.Injective g' :=
    (IsFractionRing.injective W' (FractionRing W')).comp hg
  let k : FractionRing V →+* FractionRing W' := IsFractionRing.lift (A := ν.valuationSubring) hg'
  have hk : ∀ w : ν.valuationSubring, k (w : FractionRing V) = algebraMap W' (FractionRing W') (g w) := fun w =>
    IsFractionRing.lift_algebraMap (A := ν.valuationSubring) hg' w
  refine ⟨W', inferInstance, inferInstance, inferInstance, hdvr, g.comp i, k, ⟨inferInstance, inferInstance, hc, hz⟩,
    hg.comp hiinj, inferInstance, fun v => by rw [← hi, hk]; rfl, ?_⟩
  rintro x y ⟨r, hr⟩
  by_cases hy : y = 0
  · have : k x = 0 := by rw [hr, hy, map_zero, mul_zero]
    rw [(map_eq_zero_iff k k.injective).1 this, hy]
  by_contra hxy
  rw [not_le] at hxy
  set z := x / y with hz'
  have hyν : ν y ≠ 0 := (ν.ne_zero_iff).2 hy
  have hz1 : 1 < ν z := by
    rw [hz', map_div₀]
    exact (one_lt_div₀ (zero_lt_iff.2 hyν)).2 hxy
  have hz0 : z ≠ 0 := by
    intro h; rw [h, map_zero] at hz1; exact not_lt_zero' hz1
  have hzi : ν z⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hz1
  let w : ν.valuationSubring := ⟨z⁻¹, hzi.le⟩
  have hkz : k z = algebraMap W' (FractionRing W') r := by
    rw [hz', map_div₀, hr, mul_div_assoc, div_self ((map_ne_zero k).2 hy), mul_one]
  have hkw : k (w : FractionRing V) = (k z)⁻¹ := by
    change k z⁻¹ = _
    rw [map_inv₀]
  rw [hk, hkz] at hkw
  have hunit : IsUnit (g w) := by
    have h : g w * r = 1 := by
      apply IsFractionRing.injective W' (FractionRing W')
      rw [map_mul, map_one, hkw, inv_mul_cancel₀]
      rw [← hkz]; exact (map_ne_zero k).2 hz0
    exact ⟨⟨g w, r, h, by rw [mul_comm]; exact h⟩, rfl⟩
  exact hnu w hzi (IsUnit.of_map g w hunit)

end GlobalTheory.DivBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteRegularLocalMeetOfFlatMaps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory

theorem exists_complete_regular_meet : ∀ (O R₁ R' Ω : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R₁] [IsRegularLocalRing R₁] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Field Ω] (φ₁ : O →+* R₁) (φ' : O →+* R') (u : R₁ →+* Ω) (u' : R' →+* Ω), φ₁.Flat → IsLocalHom φ₁ → IsAdicComplete (maximalIdeal R') R' → IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified → RingHom.ker u = maximalIdeal R₁ → RingHom.ker u' = maximalIdeal R' → u.comp φ₁ = u'.comp φ' → ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (_ : IsDomain E) (a : R₁ →+* E) (b : R' →+* E) (v : E →+* Ω), a.Flat ∧ b.Flat ∧ a.comp φ₁ = b.comp φ' ∧ RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ v.comp b = u' ∧ (maximalIdeal R₁).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E := by
  intro O R₁ R' Ω _ _ _ _ _ _ _ _ _ φ₁ φ' u u' hφ₁ hloc _hR' het hunr hu hu' hcomm
  obtain ⟨G, β, hGm, hGr, hGs, hspan⟩ := _root_.GlobalTheory.exists_monic_simple_root_generator_residue O R' Ω φ' u' het hunr hu'
  obtain ⟨C, _, _, c, uC, hcf, hcm, hcc, huC, huCc⟩ := _root_.GlobalTheory.RegularCompletionPackage.exists_regular_completion R₁ Ω u hu
  have hcomp : uC.comp (c.comp φ₁) = u'.comp φ' := by rw [← RingHom.comp_assoc, huCc, hcomm]
  obtain ⟨E, _, _, e, v, hef, hem, hec, hv, hve, hβ⟩ := _root_.GlobalTheory.MonicRootExtension.exists_extension C Ω uC (G.map (c.comp φ₁)) β huC hcc
    (hGm.map _) (by rw [Polynomial.map_map, hcomp]; exact hGr) (by rw [Polynomial.map_map, hcomp]; exact hGs)
  have hdom : IsDomain E := GlobalTheory.isDomain_of_isRegularLocalRing E
  have hmapE : (maximalIdeal R₁).map (e.comp c) = maximalIdeal E := by
    rw [← Ideal.map_map, hcm, hem]
  have hva : v.comp (e.comp c) = u := by rw [← RingHom.comp_assoc, hve, huCc]
  have hψl : IsLocalHom ((e.comp c).comp φ₁) := by
    refine ⟨fun x hx => ?_⟩
    by_contra h
    have h1 : φ₁ x ∈ maximalIdeal R₁ := by
      rw [mem_maximalIdeal, mem_nonunits_iff]; exact fun h' => h (isUnit_of_map_unit φ₁ x h')
    have h2 : (e.comp c) (φ₁ x) ∈ maximalIdeal E := hmapE ▸ Ideal.mem_map_of_mem _ h1
    exact (mem_maximalIdeal _).1 h2 hx
  have hv' : v.comp ((e.comp c).comp φ₁) = u'.comp φ' := by rw [← RingHom.comp_assoc, hva, hcomm]
  have hrange : ∀ r : R', u' r ∈ v.range := by
    intro r
    obtain ⟨q, hq⟩ := hspan r
    obtain ⟨y, hy⟩ := hβ
    refine ⟨Polynomial.eval₂ ((e.comp c).comp φ₁) y q, ?_⟩
    rw [hq, ← hv', Polynomial.eval_map, ← hy, Polynomial.hom_eval₂]
  obtain ⟨b, hb1, hb2⟩ := _root_.GlobalTheory.EtaleCompletionLift.exists_extension O R' E Ω φ' ((e.comp c).comp φ₁) u' v het hunr hec hψl hu' hv hv' hrange
  have hbl : IsLocalHom b := by
    refine ⟨fun r hr => ?_⟩
    by_contra h
    have h1 : r ∈ maximalIdeal R' := (mem_maximalIdeal _).2 h
    rw [← hu', RingHom.mem_ker] at h1
    have h2 : b r ∈ RingHom.ker v := by rw [RingHom.mem_ker, ← RingHom.comp_apply, hb2, h1]
    rw [hv, mem_maximalIdeal] at h2
    exact h2 hr
  have haf : (e.comp c).Flat := RingHom.Flat.comp hcf hef
  have hbf : b.Flat := _root_.GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal O R' E φ' b het.1 het.2.1 hbl (by rw [hb1]; exact RingHom.Flat.comp hφ₁ haf)
  exact ⟨E, inferInstance, inferInstance, hdom, e.comp c, b, v, haf, hbf, hb1.symm, hv, hva, hb2, hmapE, hec⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentStalkDerivationOfFunctionFieldExtStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_componentStalkDerivation_of_functionField_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), (∀ r, ρ r = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r)) → ∀ (d : Fin Dw.dim → Derivation ℤ Γ(TF.Y.X, U.1) Γ(TF.Y.X, U.1)) (D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ (d j r)) → letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∃ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j a, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField a) = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (δ j a)) ∧ ∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx (d j r) := by
  first | exact @GlobalTheory.LogKSDiv.exists_stalkDer_extend | exact GlobalTheory.LogKSDiv.exists_stalkDer_extend | (intros; apply GlobalTheory.LogKSDiv.exists_stalkDer_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinateFunctionalsFunctionFieldExtensio
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FunctionFieldCoords

theorem map_genericPoint_eq {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem functionFieldMap_finite {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W)
    [IsDominant f] (h : f.residueDegree (genericPoint M) ≠ 0) : (functionFieldMap f).Finite := by
  have hfin : (f.residueFieldMap (genericPoint M)).hom.Finite := by
    letI := (f.residueFieldMap (genericPoint M)).hom.toAlgebra
    change Module.finrank (W.residueField (f (genericPoint M))) (M.residueField (genericPoint M)) ≠ 0
      at h
    exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
  have hsurj : ∀ {x : W} (h : x ⤳ genericPoint W), x = genericPoint W →
      Function.Surjective (W.presheaf.stalkSpecializes h).hom := by
    rintro x h rfl
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact fun a => ⟨a, rfl⟩
  have hinj : Function.Injective (M.residue (genericPoint M)).hom :=
    RingHom.injective (f := ((M.residue (genericPoint M)).hom : M.functionField →+* _))
  let e := RingEquiv.ofBijective (M.residue (genericPoint M)).hom
    ⟨hinj, M.residue_surjective _⟩
  have key : ∀ (hs : f (genericPoint M) ⤳ genericPoint W),
      ((W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom).Finite := by
    intro hs
    have hc : (M.residue (genericPoint M)).hom.comp
        (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom =
        (f.residueFieldMap (genericPoint M)).hom.comp
          ((W.residue _).hom.comp (W.presheaf.stalkSpecializes hs).hom) := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
        Category.assoc, Category.assoc, Scheme.residue_residueFieldMap]
    have h1 : ((M.residue (genericPoint M)).hom.comp
        (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom).Finite := by
      rw [hc]
      exact hfin.comp (RingHom.Finite.of_surjective _
        ((W.residue_surjective _).comp (hsurj hs (map_genericPoint_eq f))))
    have h2 : (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom =
        (e.symm : _ →+* _).comp ((M.residue (genericPoint M)).hom.comp
          (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom) := by
      ext a
      exact (e.symm_apply_apply _).symm
    rw [h2]
    exact (RingHom.Finite.of_surjective _ e.symm.surjective).comp h1
  exact key _

end GlobalTheory.FunctionFieldCoords

theorem GlobalTheory.functionField_coords : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f], f.residueDegree (genericPoint M) ≠ 0 → ∃ (r : ℕ) (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) ∧ ∀ x, (∀ j, co j x = 0) → x = 0 := by
  intro M W _ _ f _ h
  letI := (functionFieldMap f).toAlgebra
  haveI : Module.Finite W.functionField M.functionField :=
    GlobalTheory.FunctionFieldCoords.functionFieldMap_finite f h
  let b := Module.finBasis W.functionField M.functionField
  refine ⟨Module.finrank W.functionField M.functionField, fun j => (b.coord j).toAddMonoidHom,
    fun j c x => ?_, fun x hx => ?_⟩
  · change b.coord j (c • x) = c * b.coord j x
    rw [map_smul, smul_eq_mul]
  · exact b.ext_elem fun i => by simpa using hx i
end
end

