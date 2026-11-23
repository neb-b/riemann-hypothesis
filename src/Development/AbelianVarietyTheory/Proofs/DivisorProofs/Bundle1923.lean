module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicUniformizationComplexBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.UnifTan

theorem valR_comp_eq {A : Type} [CommRing A] {X Y : Scheme.{0}} (p : Sp A ⟶ X) (ψ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valR (p ≫ ψ) U f = valR p (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
  first
  | exact @_root_.GlobalTheory.ValuationCompositionDivisor.valR_comp
  | exact _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp
  | (apply _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationCompositionDivisor.valR_comp <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp ..)

theorem valF_eq_valAt' {X : Scheme.{0}} (p : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF p U f = valAt' p U f := by
  unfold valF valAt' valAt
  split_ifs <;> rfl

theorem valR_eq_valAt' {X : Scheme.{0}} (p : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valR p U f = valAt' p U f := by
  unfold valR valAt' valAt
  split_ifs <;> rfl

theorem valAt'_comp_eq {X Y : Scheme.{0}} (p : Sp ℂ ⟶ X) (ψ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (p ≫ ψ) U f = valAt' p (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
  rw [← valR_eq_valAt', ← valR_eq_valAt', valR_comp_eq]

theorem prime_subsingleton : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := by
  constructor
  have key : ∀ (P : PrimeSpectrum (DualNumber ℂ)) (z : DualNumber ℂ), z ∈ P.asIdeal ↔ z.fst = 0 := by
    intro P z
    constructor
    · intro hz
      by_contra hne
      have hu : IsUnit z := (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (isUnit_iff_ne_zero.2 hne)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz hu)
    · intro hz
      have h2 : z * z = 0 := by
        ext <;> simp [hz]
      have : z * z ∈ P.asIdeal := by rw [h2]; exact P.asIdeal.zero_mem
      rcases P.isPrime.mem_or_mem this with h | h <;> exact h
  intro P Q
  ext z
  rw [key P, key Q]

theorem top_le_of_red {X : Scheme.{0}} (p : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) (h : ⊤ ≤ (redE ℂ ≫ p) ⁻¹ᵁ U) :
    ⊤ ≤ p ⁻¹ᵁ U := by
  intro y _
  have hy : y = redE ℂ (IsLocalRing.closedPoint ℂ) := by
    haveI := prime_subsingleton
    exact Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) _ _
  have := h (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  rw [hy]
  exact this

theorem tf_hom (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] :
    (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
  simp only [TF, jFK, jK, Over.mk_hom, spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem ex_zero {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    (u.ex 0).left = η[A].left := by
  have h1 : u.ex 0 = 1 := by
    have := u.ex_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  rw [h1, Hom.one_def]
  simp

theorem isD_iff_isDiff : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (N : NumD ℂ)
    (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ D.P.A.left),
    IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ → (∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ) →
    ∀ (b' : epsR ℂ ⟶ x.P.A) (b : TE R ℂ ⟶ D.P.A), IsTangent b' → b'.left ≫ φ = b.left →
      ∀ W' : Fin g → ℂ, (IsD ν d W' b ↔ u.IsDiff W' b') := by
  intro R _ _ _ D N ν g d x u φ hφ hE b' b hb' hbb W'
  have hP : IsPullback x.P.A.hom φ (TF (R := R) ℂ).hom D.P.A.hom := by
    rw [tf_hom]; exact hφ.1.flip
  let e := hP.isoPullback
  let ψ : x.P.A.left ⟶ (DegPre.BF D ℂ).left := e.hom
  have hψi : ψ ≫ e.inv = 𝟙 _ := e.hom_inv_id
  have hpt : ∀ z, ptB ν d z = (u.ex z).left ≫ ψ := by
    intro z
    apply pullback.hom_ext
    · simp only [ptB, Over.lift_left, pullback.lift_fst, Category.assoc, ψ, e, IsPullback.isoPullback_hom_fst]
      have := Over.w (u.ex z)
      simpa using this.symm
    · simp only [ptB, Over.lift_left, pullback.lift_snd, Category.assoc, ψ, e, IsPullback.isoPullback_hom_snd]
      exact hE z
  have hb : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left = b'.left ≫ ψ := by
    apply pullback.hom_ext
    · simp only [Over.lift_left, pullback.lift_fst, Category.assoc, ψ, e, IsPullback.isoPullback_hom_fst, Over.homMk_left]
      have := Over.w b'
      simpa using this.symm
    · simp only [Over.lift_left, pullback.lift_snd, Category.assoc, ψ, e, IsPullback.isoPullback_hom_snd]
      exact hbb.symm
  have hred : redE ℂ ≫ b'.left = (u.ex 0).left := by
    rw [ex_zero]; exact hb'
  have back : ∀ {A : Type} [CommRing A] (p : Sp A ⟶ x.P.A.left) (U' : x.P.A.left.Opens) (f' : Γ(x.P.A.left, U')),
      valR (p ≫ ψ) (e.inv ⁻¹ᵁ U') ((e.inv.app U').hom f') = valR p U' f' := by
    intro A _ p U' f'
    rw [← valR_comp_eq, Category.assoc, hψi, Category.comp_id]
  have valB : ∀ (U' : x.P.A.left.Opens) (h : ⊤ ≤ b'.left ⁻¹ᵁ U') (f' : Γ(x.P.A.left, U')),
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((b'.left.appLE U' ⊤ h).hom f') = valR b'.left U' f' := by
    intro U' h f'
    unfold valR
    rw [dite_eq_left h]
  constructor
  · intro hD U' h f'
    have h0 : ⊤ ≤ ptB ν d 0 ⁻¹ᵁ (e.inv ⁻¹ᵁ U') := by
      have hc : (((u.ex 0).left ≫ ψ) ≫ e.inv) = redE ℂ ≫ b'.left := by
        rw [Category.assoc, hψi, Category.comp_id, hred]
      rw [hpt 0]
      show ⊤ ≤ (((u.ex 0).left ≫ ψ) ≫ e.inv) ⁻¹ᵁ U'
      rw [hc]
      exact fun y _ => h (Set.mem_univ ((redE ℂ) y))
    have k := hD _ ((e.inv.app U').hom f') h0
    simp only [hb, hpt, valF_eq_valAt', ← valR_eq_valAt', back] at k
    rw [valB U' h f', k]
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, valR_eq_valAt']
  · intro hI U f h0
    have h1 : ⊤ ≤ b'.left ⁻¹ᵁ (ψ ⁻¹ᵁ U) := by
      apply top_le_of_red
      rw [hred]
      rw [hpt] at h0
      exact h0
    have hs := hI (ψ ⁻¹ᵁ U) h1 ((ψ.app U).hom f)
    rw [valB] at hs
    simp only [hb, hpt, valR_comp_eq, valF_eq_valAt', valAt'_comp_eq]
    ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
      rw [← hred, ← valR_eq_valAt', (GlobalTheory.ZH.CrdCalc.valR_spMap _ _ _ h1).2]
      rfl
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      exact hs

end GlobalTheory.UnifTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataMapSupComapClosedImmersion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.ClosedImmIdeal

theorem ideal_comap_preimage {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i]
    (J : W.IdealSheafData) (U : W.affineOpens) :
    (J.comap i).ideal ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ = Ideal.map (i.app U.1).hom (J.ideal U) := by
  rw [GlobalTheory.Principalise.comapIdealAffine J i U ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ le_rfl,
    Scheme.Hom.app_eq_appLE]

theorem iSup_preimage_affineOpens {T W : Scheme.{0}} (i : T ⟶ W) :
    ⨆ U : W.affineOpens, i ⁻¹ᵁ U.1 = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

theorem comap_map_eq {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i] (a : T.IdealSheafData) :
    (a.map i).comap i = a := by
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun U : W.affineOpens => ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩) (iSup_preimage_affineOpens i) fun U => ?_
  rw [ideal_comap_preimage, Scheme.IdealSheafData.ideal_map_of_isAffineHom,
    Ideal.map_comap_of_surjective _ (i.app_surjective U.1 U.2)]

theorem map_comap_eq {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i] (b : W.IdealSheafData)
    (hb : (⊥ : T.IdealSheafData).map i ≤ b) : (b.comap i).map i = b := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_map_comap _ _)
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : W.affineOpens => U)
    (iSup_affineOpens_eq_top W) fun U => ?_
  have h0 := hb U
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom] at h0 ⊢
  rw [ideal_comap_preimage, Ideal.comap_map_of_surjective _ (i.app_surjective U.1 U.2)]
  refine sup_le le_rfl (le_trans ?_ h0)
  simp

theorem map_sup_comap_and_comap_map : ∀ (T W : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i →
    ∀ (a : T.IdealSheafData) (J : W.IdealSheafData),
      (a ⊔ J.comap i).map i = a.map i ⊔ J ∧ (a.map i).comap i = a := by
  intro T W i hi a J
  haveI := hi
  refine ⟨?_, comap_map_eq i a⟩
  have hb : (⊥ : T.IdealSheafData).map i ≤ a.map i ⊔ J :=
    le_sup_of_le_left (Scheme.IdealSheafData.map_mono i bot_le)
  rw [← map_comap_eq i _ hb, Scheme.IdealSheafData.comap_sup, comap_map_eq]

end GlobalTheory.ClosedImmIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledUnitaryVacuumTensorEigen
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertDblLine

theorem line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
      IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M'.vac v) R →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw dd omd hdd hsp R hR g hg
  obtain ⟨hvSB, hv0, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
  set φ₀ := boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)) with hφ₀
  set r₀ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ := boxFun R (fun x => star (R x)) with hr₀
  have hΦ : GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) = tens (evFin F v) φ₀ r₀ := by
    funext x
    show (_ * _) * star (_ * _) = (_ * _) * (_ * _)
    rw [star_mul']
    exact mul_mul_mul_comm _ _ _ _
  have hstar : (fun x => star (G.M'.vac v x)) ∈ SB (Fin a' × Fin (a + a') → Fv F v) :=
    ⟨hvSB.1.comp star, hvSB.2.comp_left (g := star) (star_zero ℂ)⟩
  have hφ₀SB : φ₀ ∈ SB _ := GlobalTheory.BoxSpan.boxFun_mem_SB' hvSB hstar
  have hRest : Rest (evFin F v) φ₀ r₀ := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hl : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hr : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      simp only [hr₀, boxFun]
      rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
        show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hR.1 _ _ hl, hR.1 _ _ hr]
    · rw [← hΦ]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ hR.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ _ hR.2)
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.doubledWeilRepresentation_locality_finitePlace F E σ B a a' G X om om' hTr v dd omd hsp g hg.1 φ₀ hφ₀SB
  have h₀ := GlobalTheory.T.doubledVacuum_twistedVacuumCondition_doubledLattice F E σ B a a' G X om om' hTr v dd hdd θ hθ hvac
  have h₁ := GlobalTheory.T.doubledVacuumCondition_stable_latticeStabilizer_inert F E σ B a a' G X om om' hTr v dd omd hsp θ hθ g hg φ₀ hφ₀SB φ₁ hφ₁ h₀ hact
  obtain ⟨c, hc⟩ := GlobalTheory.T.inertPlace_doubledVacuumCondition_unique F E σ B a a' G X om om' hTr v w hw dd hdd θ hθ hvac φ₁ hφ₁ h₁
  refine ⟨c, ?_⟩
  rw [hΦ, hact r₀ hRest, hc]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.InertDblLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerExponentSectionMulEqZeroImpEqZero
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
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SecRingNonZeroDiv

open GlobalTheory.CompHt GlobalTheory.FlagTan

theorem eq_zero_of_mul_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (e : Ix Dw → ℤ) (F : Rul Xo c), F ∈ secZ Xo c e → (∀ Z : Comp Xo c, ∃ y : FrPt Xo c ℂ, LiesOn Z y ∧ evR Xo c F y ≠ 0) → ∀ f ∈ secRing Xo c, F * f = 0 → f = 0 := by
  intro E _ _ _ H Dw l Xo c e F hF hZ f hf hFf
  classical
  have hG : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  have hFZ : ∀ Z : Comp Xo c, genVal Z F ≠ 0 := by
    intro Z h0
    obtain ⟨y, hy, hne⟩ := hZ Z
    exact hne ((genVal_eq_zero_iff E H Dw l Xo c Z e F hF).1 h0 ℂ y hy)
  have hf' : f ∈ ⨆ e, secZ Xo c e := by rw [← GlobalTheory.LevDesc.toSubmodule_secRing]; exact hf
  obtain ⟨a, ha, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).1 hf'
  have key : ∀ Z : Comp Xo c, ∀ d ∈ a.support, genVal Z (a d) = 0 := by
    intro Z
    haveI : CharZero (Om Z) := charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
    let χ : (Ix Dw → ℤ) → ((Ix Dw → (Om Z)ˣ) →* Om Z) := fun d =>
      { toFun := fun t => ((∏ i, t i ^ d i : (Om Z)ˣ) : Om Z)
        map_one' := by simp
        map_mul' := fun t s => by simp [mul_zpow, Finset.prod_mul_distrib] }
    have hχ : Function.Injective χ := by
      intro d d' hdd
      funext i
      let u : (Om Z)ˣ := Units.mk0 2 two_ne_zero
      have hp : ∀ d : Ix Dw → ℤ, χ d (Pi.mulSingle i u) = (2 : Om Z) ^ d i := by
        intro d
        show ((∏ j, (Pi.mulSingle i u : Ix Dw → (Om Z)ˣ) j ^ d j : (Om Z)ˣ) : Om Z) = _
        rw [Finset.prod_eq_single i]
        · simp [u, Units.val_zpow_eq_zpow_val]
        · intro j _ hj
          simp [Pi.mulSingle_eq_of_ne hj]
        · simp
      have h1 : (2 : Om Z) ^ d i = (2 : Om Z) ^ d' i := by
        rw [← hp, ← hp, hdd]
      have h2 : (((2 : ℚ) ^ d i : ℚ) : Om Z) = (((2 : ℚ) ^ d' i : ℚ) : Om Z) := by
        rw [Rat.cast_zpow, Rat.cast_zpow, Rat.cast_ofNat]; exact h1
      exact zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num) (Rat.cast_injective h2)
    have hli : LinearIndependent (Om Z) (fun d => (χ d : (Ix Dw → (Om Z)ˣ) → Om Z)) :=
      (linearIndependent_monoidHom _ (Om Z)).comp χ hχ
    have hsum : ∑ d ∈ a.support, genVal Z (a d) • (χ d : (Ix Dw → (Om Z)ˣ) → Om Z) = 0 := by
      funext t
      obtain ⟨y', hy'⟩ := SecSeparation.exists_frBor (genFr hG Z) t
      have h1 : evR Xo c (F * a.sum fun _ x => x) y' = 0 := by rw [hFf]; exact evalAt_zero _ _ y'
      have h2 : evR Xo c (F * a.sum fun _ x => x) y' = evR Xo c F y' * evR Xo c (a.sum fun _ x => x) y' :=
        evalAt_mul _ _ _ _ y'
      have h3 : evR Xo c F y' ≠ 0 := by
        rw [evR_frBor hF hy']
        exact mul_ne_zero (Units.ne_zero _) (hFZ Z)
      have h4 : evR Xo c (a.sum fun _ x => x) y' = 0 := (mul_eq_zero.1 (h2.symm.trans h1)).resolve_left h3
      have h5 : evR Xo c (a.sum fun _ x => x) y' = ∑ d ∈ a.support, evR Xo c (a d) y' :=
        map_sum (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y') _ _
      rw [h5] at h4
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h4]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [evR_frBor (ha d) hy', mul_comm]
      rfl
    intro d hd
    exact linearIndependent_iff'.1 hli a.support (fun d => genVal Z (a d)) hsum d hd
  refine Finset.sum_eq_zero fun d hd => ?_
  exact secZ_eq_zero_of_genVal (ha d) fun Z => key Z d hd

end GlobalTheory.SecRingNonZeroDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombinationIffOfSameVecs
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem isCombination_pull_iff {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x : Sp R ⟶ S') (y : Sp R ⟶ S)
    (hy : y = x ≫ f) {n : ℕ} (a : Fin n → R) (V : Fin n → (Sp (DualNumber R) ⟶ G'.left))
    (hV : ∀ k, V k ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x)
    (U : Fin n → (Sp (DualNumber R) ⟶ G.left)) (hU : ∀ k, V k ≫ φ = U k)
    (w : FramedFlatCoordinates.epsAt x ⟶ G') (w' : FramedFlatCoordinates.epsAt y ⟶ G) (hw : w.left ≫ φ = w'.left) :
    FramedFlatCoordinates.IsCombination x a V w ↔ FramedFlatCoordinates.IsCombination y a U w' := by
  subst hy
  obtain rfl : U = fun k => V k ≫ φ := funext fun k => (hU k).symm
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (FramedFlatCoordinates.epsAt x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain rfl : w' = e w := Over.OverMorphism.ext (hw.symm.trans (he _).symm)
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (k : Fin n) (u : FramedFlatCoordinates.epsAt x ⟶ G'), u.left = spMap (epsScaleR (a k)) ≫ V k ↔
      (e u).left = spMap (epsScaleR (a k)) ≫ V k ≫ φ := fun k u => by
    rw [he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR (a k)) ≫ ·) (hV k)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc (a k)))
  have pr : ∀ u : Fin n → (FramedFlatCoordinates.epsAt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod :=
    fun u => by rw [map_list_prod, List.map_ofFn]; rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => e (u i), fun i => (hR _ _).1 (hu i), pr u⟩
  · rintro ⟨u, hu, hw⟩
    refine ⟨fun i => e.symm (u i), fun i => (hR _ _).2 (by rw [e.apply_symm_apply]; exact hu i), e.injective ?_⟩
    rw [pr]
    simp only [MulEquiv.apply_symm_apply]
    exact hw

theorem isCombination_iff_of_sameVecs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (x : Sp R ⟶ Xo.XF c) (x' : Sp R' ⟶ Xo.XF c) (n : ℕ) (v : Fin n → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)) (vb : Fin n → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)) (v' : Fin n → (epsAt (x' ≫ toX Xo c) ⟶ Xo.univ.t.G)) (vb' : Fin n → (epsAt ((x' ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)), x' = spMap g ≫ x → SameVecs Y x v vb → SameVecs Y x' v' vb' → ∀ (a : Fin n → R') (i : Fin n), FramedFlatCoordinates.IsCombination (x' ≫ toX Xo c) a (fun k => spMap (Chart.dualMapR g) ≫ (v k).left) (v' i) ↔ FramedFlatCoordinates.IsCombination ((x' ≫ Y.jQ) ≫ genι Y) a (fun k => spMap (Chart.dualMapR g) ≫ (vb k).left) (vb' i) := by
  intro E _ _ _ H D l Xo c O _ β Y R R' _ _ g x x' n v vb v' vb' hx h h' a i
  choose v₁ h₁ h₂ using h
  obtain ⟨w, hw₁, hw₂⟩ := h' i
  have hV : ∀ k, (spMap (Chart.dualMapR g) ≫ (v₁ k).left) ≫ Y.oF.t.G.hom =
      spMap (algebraMap R' (DualNumber R')) ≫ x' := fun k => by
    subst hx
    exact Over.w (DetExtendZero.epsMap g x ≫ v₁ k)
  refine (isCombination_pull_iff Y.m0.toSABMap.cart x' _ rfl a _ hV _ (fun k => ?_) w _ hw₁).symm.trans
    (isCombination_pull_iff Y.m.cart x' _ (Category.assoc _ _ _) a _ hV _ (fun k => ?_) w _ hw₂)
  · exact (Category.assoc _ _ _).trans (congrArg (spMap (Chart.dualMapR g) ≫ ·) (h₁ k))
  · exact (Category.assoc _ _ _).trans (congrArg (spMap (Chart.dualMapR g) ≫ ·) (h₂ k))

end GlobalTheory.DetLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEigenvectorIntegralOfTangentPullbackMem
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanEigInt

theorem isEigV_of_tanPull_mem : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (x : Sp T.V ⟶ Y.X) (x' : Sp T.Fr ⟶ Y.X) (e : spMap (algebraMap T.V T.Fr) ≫ x = x'), Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) → ∀ (G : SAB H (Sp T.V)) (ψ : SABMap G Y.t x) (τ : E →+* ℂ) (w : epsOver T.V T.V ⟶ G.G) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ → GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e v ∈ GlobalTheory.FlagMod.eigLie c x' τ → IsEigV c io G τ w := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io x x' e hinj G ψ τ w v hv hmem a z hz
  have h1 : ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a v = z • v := by
    apply hinj
    rw [GlobalTheory.FlagMod.tanPull_actR, map_smulₛₗ, hmem a, hz]
    rfl
  have h2 : (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left ≫ (Y.t.act.act a).left =
      spMap (epsMul z) ≫ (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left :=
    congrArg (fun u => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv u).left) h1
  have hc : (epsMul z).comp ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) =
      (algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V) :=
    RingHom.ext fun r => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  apply ψ.cart.1.hom_ext
  · rw [Over.comp_left, Category.assoc, ψ.act a, ← Category.assoc, ← hv, h2, hv, Category.assoc]
  · rw [Over.comp_left, Category.assoc, Over.w, Over.w, Category.assoc, Over.w]
    show spMap _ = spMap (epsMul z) ≫ spMap _
    rw [spMap_comp', hc]

end GlobalTheory.TanEigInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralGeometricallyConnectedOpenModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem isIntegral_open_of_geometricallyConnected :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H)
      (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens),
      GeometricallyConnected (U.ι ≫ toF Xo c) → IsIntegral U.toScheme := by
  intro E _ _ _ H D l Xo c U hU
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : Smooth (toF Xo c) := inferInstanceAs (Smooth (pullback.snd _ _))
  have : ConnectedSpace U.toScheme :=
    GeometricallyConnected.connectedSpace_of_subsingleton (U.ι ≫ toF Xo c)
  exact GlobalTheory.isIntegral_of_smooth_field (U.ι ≫ toF Xo c)

end GlobalTheory.DetLine
end

