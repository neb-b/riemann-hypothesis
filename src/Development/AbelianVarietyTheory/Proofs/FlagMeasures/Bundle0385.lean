module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0380
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeVolumeEqOfSemilinearIsometryGenus
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SymmMemOfMem
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianVolumeDependsOnlyOnFieldSignature
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.VolInvariant

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J y x = star y ⬝ᵥ (J *ᵥ x) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem eq_or_conj {E : Type} [Field E] [CharZero E] [StarRing E] (φ ψ : E →+* ℂ)
    (hψ : ∀ a, ψ (star a) = starRingEnd ℂ (ψ a)) (h : ∀ a, star a = a → φ a = ψ a) :
    φ = ψ ∨ φ = (starRingEnd ℂ).comp ψ := by
  by_cases hall : ∀ a : E, star a = a
  · left; ext a; exact h a (hall a)
  push Not at hall
  obtain ⟨b, hb⟩ := hall
  set θ := b - star b with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 hb.symm
  have hs : star θ = -θ := by simp [hθ]
  have hsq : φ θ ^ 2 = ψ θ ^ 2 := by
    rw [← map_pow, ← map_pow]; apply h; rw [star_pow, hs]; ring
  have h2 : star (2 : E) = 2 := star_ofNat 2
  have dec : ∀ a : E, ∃ u w : E, star u = u ∧ star w = w ∧ a = u + θ * w := by
    intro a
    refine ⟨(a + star a) / 2, (a - star a) / (2 * θ), ?_, ?_, ?_⟩
    · rw [star_div₀, star_add, star_star, h2, add_comm]
    · rw [star_div₀, star_sub, star_star, star_mul', h2, hs]; field_simp; ring
    · field_simp; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | h1
  · left; ext a
    obtain ⟨u, w, hu, hw, rfl⟩ := dec a
    simp only [map_add (f := _), map_mul, h u hu, h w hw, h1]
  · right; ext a
    obtain ⟨u, w, hu, hw, rfl⟩ := dec a
    rw [RingHom.comp_apply, ← hψ, star_add, star_mul', hu, hw, hs]
    simp only [map_add (f := _), map_mul, map_neg, h u hu, h w hw, h1]

theorem hasSignature_all (I : AutInst) {p q : ℕ} (h : HasSig I p q) (φ : I.E →+* ℂ) :
    Formalism.UG.HasSignature (I.J.map φ) p q := by
  set v : InfinitePlace I.F := InfinitePlace.mk (φ.comp (algebraMap I.F I.E)) with hv
  have hc := I.cm.cmUnram.2.1
  have hag : ∀ a, star a = a → φ a = I.φ v a := by
    intro a ha
    obtain ⟨c, rfl⟩ := (I.cm.fixed a).1 ha
    rw [I.φ_over]
    rcases InfinitePlace.embedding_mk_eq (φ.comp (algebraMap I.F I.E)) with h1 | h1
    · rw [hv, h1]; rfl
    · rw [hv, h1, ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hc, ha]
  rw [← (h v).1, ← (h v).2]
  rcases eq_or_conj φ (I.φ v) (hc _) hag with h1 | h1
  · have e0 : I.J.map φ = I.J.map (I.φ v) := congrArg (fun ψ : I.E →+* ℂ => I.J.map ψ) h1
    rw [e0]
    exact GlobalTheory.AutInhab.hasSignature_inst I v
  · refine GlobalTheory.AutInhab.hasSignature_of_frame (P := (I.P v).map (starRingEnd ℂ)) ?_ ?_
    · exact (I.P_unit v).map (starRingEnd ℂ).mapMatrix
    · have := congrArg (fun M => Matrix.map M (starRingEnd ℂ)) (I.P_spec v)
      simp only [Matrix.map_mul] at this
      have e1 : I.J.map φ = (I.J.map (I.φ v)).map (starRingEnd ℂ) := by
        ext i j; conv_lhs => rw [h1]
        rfl
      have e2 : ((I.P v).map (starRingEnd ℂ))ᴴ = ((I.P v)ᴴ).map (starRingEnd ℂ) := by
        ext i j; rfl
      rw [e1, e2, this]
      ext i j
      simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
      split_ifs <;> simp

section Transport

variable {E E' : Type} [Field E] [NumberField E] [StarRing E] [Field E'] [NumberField E'] [StarRing E'] {n : ℕ}

theorem exists_image (e : E' ≃+* E) (he : ∀ y, e (star y) = star (e y)) (J : Matrix (Fin n) (Fin n) E)
    (J' : Matrix (Fin n) (Fin n) E') (A : GL (Fin n) E)
    (hA : (A : Matrix (Fin n) (Fin n) E)ᴴ * J * (A : Matrix (Fin n) (Fin n) E) = J'.map e)
    (L : Submodule (𝓞 E') (Fin n → E')) (hL : Submodule.IsLattice E' L)
    (hd : ∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (J' *ᵥ x) ∈ (algebraMap (𝓞 E') E').range) :
    ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧
      (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) ∧
      ∀ y : Fin n → E', y ∈ L ↔ (A : Matrix (Fin n) (Fin n) E) *ᵥ (fun i => e (y i)) ∈ Λ := by
  let σ : 𝓞 E' →+* 𝓞 E := (RingOfIntegers.mapRingEquiv e : 𝓞 E' ≃+* 𝓞 E)
  haveI : RingHomSurjective σ := ⟨(RingOfIntegers.mapRingEquiv e).surjective⟩
  haveI : RingHomSurjective (e : E' →+* E) := ⟨e.surjective⟩
  let g : (Fin n → E') →ₛₗ[(e : E' →+* E)] (Fin n → E) :=
    { toFun := fun y => (A : Matrix (Fin n) (Fin n) E) *ᵥ (fun i => e (y i))
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add]; congr 1; ext i; simp
      map_smul' := fun c x => by
        rw [← Matrix.mulVec_smul]; congr 1; ext i; simp }
  let f : (Fin n → E') →ₛₗ[σ] (Fin n → E) :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun c x => g.map_smulₛₗ (c : E') x }
  have hf : ∀ y, f y = (A : Matrix (Fin n) (Fin n) E) *ᵥ (fun i => e (y i)) := fun _ => rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun z => ((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ z) hxy
    simp only [hf, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
    ext i; exact e.injective (congrFun this i)
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨fun i => e.symm ((((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) i), ?_⟩
    simp only [hf, RingEquiv.apply_symm_apply]
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hform : ∀ x y, star (f y) ⬝ᵥ (J *ᵥ f x) = e (star y ⬝ᵥ (J' *ᵥ x)) := by
    intro x y
    rw [hf, hf, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
    simp [dotProduct, Matrix.mulVec, he]
  have hint : ∀ a : E', e a ∈ (algebraMap (𝓞 E) E).range ↔ a ∈ (algebraMap (𝓞 E') E').range := by
    intro a
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨(RingOfIntegers.mapRingEquiv e).symm c, e.injective ?_⟩
      rw [← hc]
      exact e.apply_symm_apply _
    · rintro ⟨c, rfl⟩
      exact ⟨σ c, rfl⟩
  have hmem : ∀ y, y ∈ L ↔ f y ∈ L.map f := fun y =>
    ⟨fun h => ⟨y, h, rfl⟩, fun ⟨z, hz, h⟩ => hinj h ▸ hz⟩
  refine ⟨L.map f, Submodule.IsLattice.of_fg E (hL.fg.map f), ?_, hmem⟩
  · intro x
    obtain ⟨x, rfl⟩ := hsurj x
    rw [← hmem, hd]
    constructor
    · rintro h _ ⟨y, hy, rfl⟩
      rw [hform, hint]; exact h y hy
    · intro h y hy
      rw [← hint, ← hform]; exact h _ ⟨y, hy, rfl⟩

theorem exists_isometry (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (e : E' ≃+* E) (he : ∀ y, e (star y) = star (e y)) {n' : ℕ}
    (hn : n' = n) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E')
    (hJ : Jᴴ = J) (hJ' : J'ᴴ = J') (hdet : J.det ≠ 0) (hdet' : J'.det ≠ 0)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (hd : ∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range)
    (L' : Submodule (𝓞 E') (Fin n' → E')) (hL' : Submodule.IsLattice E' L')
    (hd' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', star y ⬝ᵥ (J' *ᵥ x) ∈ (algebraMap (𝓞 E') E').range)
    {p q : ℕ} (hs : ∀ φ : E →+* ℂ, Formalism.UG.HasSignature (J.map φ) p q)
    (hs' : ∀ φ : E' →+* ℂ, Formalism.UG.HasSignature (J'.map φ) p q) :
    ∃ (A : Matrix (Fin n) (Fin n') E) (Λ : Submodule (𝓞 E) (Fin n → E)), Aᴴ * J * A = J'.map e ∧
      Submodule.IsLattice E Λ ∧
      (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) ∧
      ∀ y : Fin n' → E', y ∈ L' ↔ A *ᵥ (fun i => e (y i)) ∈ Λ := by
  subst hn
  obtain ⟨Λ₁, h1, h2, -⟩ := exists_image e he (J'.map e) J' 1 (by simp) L' hL' hd'
  have hh : (J'.map e)ᴴ = J'.map e := by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← he, ← Matrix.conjTranspose_apply, hJ']
  have hde : (J'.map e).det ≠ 0 := by
    have := RingHom.map_det (e : E' →+* E) J'
    rw [RingHom.mapMatrix_apply] at this
    have h3 : (J'.map e).det = e J'.det := this.symm
    rw [h3]
    exact (map_ne_zero e).2 hdet'
  obtain ⟨γ, hγ⟩ := _root_.GlobalTheory.FlagMeas.sameKindIsometric E hE _ J (J'.map e) hJ hh hdet hde ⟨L, hL, hd⟩ ⟨Λ₁, h1, h2⟩
    fun φ => ⟨p, q, hs φ, hs' (φ.comp (e : E' →+* E))⟩
  obtain ⟨Λ, h3, h4, h5⟩ := exists_image e he J J' γ hγ L' hL' hd'
  exact ⟨γ, Λ, hγ, h3, h4, h5⟩

end Transport

theorem rank_eq (I : AutInst) {p q : ℕ} (h : HasSig I p q) : I.n = p + q := by
  obtain ⟨φ⟩ : Nonempty (I.E →+* ℂ) := inferInstance
  simpa using (Formalism.UG.P.sig_data _ p q (hasSignature_all I h φ)).1

theorem volumeInvariant : VolumeInvariant := by
  rintro I I' p q ⟨e, he⟩ h h' c μf _ _ c' μf' _ _ hc hc'
  have hn : I'.n = I.n := (rank_eq I' h').trans (rank_eq I h).symm
  obtain ⟨A, Λ, hA, hΛ, hd, hmem⟩ := exists_isometry I.cm.cmUnram e he hn I.J I'.J I.J_herm I'.J_herm
    I.J_det I'.J_det I.L (Submodule.IsLattice.of_fg I.E I.L_fg) (by simpa only [hform_eq] using I.L_dual)
    I'.L (Submodule.IsLattice.of_fg I'.E I'.L_fg) (by simpa only [hform_eq] using I'.L_dual)
    (hasSignature_all I h) (hasSignature_all I' h')
  obtain ⟨xf, hx⟩ := _root_.GlobalTheory.SelfDualPoint.exists_lamX_eq I Λ hΛ (by simpa only [hform_eq] using hd)
  exact _root_.GlobalTheory.GaugeTransport.gaugeVol_transport I I' e A xf he hn hA (hx ▸ hmem) c μf c' μf' hc hc'

end GlobalTheory.VolInvariant
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrincipalCongruenceMapCompletionSubOneValuedLt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem GLp.inc_map_sub_one_valued_lt_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, ‖θ z‖ < 1 → Valued.v z < 1) → ∀ k ∈ (GlobalTheory.GLp.red g n).ker, ∀ a b : Fin n, Valued.v ((Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n k) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - (((((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1 := by
  intro F _ _ v g n _ θ hθ k hk a b
  have hk' : PadicInt.toZMod ((k : Matrix (Fin n) (Fin n) ℤ_[g]) a b) =
      ((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b := by
    have := congrArg (fun x : GL (Fin n) (ZMod g) => (x : Matrix (Fin n) (Fin n) (ZMod g)) a b)
      (MonoidHom.mem_ker.mp hk)
    simpa [GlobalTheory.GLp.red] using this
  set c : ℕ := (((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val with hc
  have hmem : (k : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g]) ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
    rw [RingHom.mem_ker, map_sub, hk', map_natCast, hc, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod] at hmem
  have hnorm : ‖(k : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g])‖ < 1 := PadicInt.mem_nonunits.mp hmem
  apply hθ
  have he : θ ((Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n k) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - (c : v.adicCompletion F)) =
      (((k : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g]) : ℤ_[g]) : ℚ_[g]) := by
    simp [GlobalTheory.GLp.inc, Matrix.GeneralLinearGroup.map]
  rw [he, PadicInt.padic_norm_e_of_padicInt]
  exact hnorm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitTrivialTranslateLocalComponentDisjointOrLe
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.SlocDich.translate_dichotomy : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)), Function.Injective T → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)) → ∀ y : GAf L n, TrivOutside {s.v}ᶜ y → ∀ P : Submodule ℂ (GAf L n → ℂ), (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ P, NG.rt L n x f ∈ P) → Disjoint (LinearMap.range ((NG.rt L n y).comp T)) P ∨ LinearMap.range ((NG.rt L n y).comp T) ≤ P := by
  intro L _ _ _ n s τ i T _hTi hT y hy P hP
  have hpart := _root_.GlobalTheory.SplitAdelic.main L n s

  have hstab : ∀ (g : GL (Fin n) (s.w.adicCompletion L)) (a : τ.V),
      a ∈ P.comap ((NG.rt L n y).comp T) → τ.ρ g a ∈ P.comap ((NG.rt L n y).comp T) := by
    intro g a ha
    obtain ⟨x, ⟨hx, hxA⟩, -⟩ := hpart.2.2 (Matrix.GeneralLinearGroup.map i.symm.toRingHom g)
    have hg : g = Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x) := by
      rw [hxA]; ext j k; simp
    have hc := hpart.2.1 x y hx hy
    simp only [Submodule.mem_comap, LinearMap.comp_apply] at ha ⊢
    rw [hg, hT x hx a]
    have e : NG.rt L n y (NG.rt L n x (T a)) = NG.rt L n x (NG.rt L n y (T a)) := by
      funext g'
      show T a (g' * y * x) = T a (g' * x * y)
      rw [mul_assoc, mul_assoc, hc.eq]
    rw [e]
    exact hP x hx _ ha
  let Q : Subrepresentation τ.ρ := ⟨P.comap ((NG.rt L n y).comp T), hstab⟩
  rcases τ.irr.eq_bot_or_eq_top Q with h | h
  · left
    rw [Submodule.disjoint_def]
    rintro f ⟨a, rfl⟩ hf
    have ha : a ∈ Q.toSubmodule := hf
    rw [h] at ha
    have : a = 0 := ha
    simp [this]
  · right
    rintro f ⟨a, rfl⟩
    have ha : a ∈ Q.toSubmodule := by rw [h]; trivial
    exact ha
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowDoubleCosetEqIffIsometries
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.KeyIff

variable {D : D7}

theorem one_mem {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : (1 : GV D) ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, fun j x _ => ?_, fun x _ => ?_⟩
  · simp
  · simp

theorem dcoset_eq_iff {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (γ₁ γ₂ : GV D) :
    ({δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₁ * n'} : Set (GV D)) =
        {δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₂ * n'} ↔
      ∃ n ∈ NRat F, ∃ n' ∈ NRat F', γ₂ = n * γ₁ * n' := by
  constructor
  · intro h
    have hm : γ₂ ∈ {δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₂ * n'} :=
      ⟨1, one_mem F, 1, one_mem F', by simp⟩
    rw [← h] at hm
    exact hm
  · rintro ⟨n, hn, n', hn', rfl⟩
    ext δ
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * n⁻¹, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F ha (Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv F hn),
        n'⁻¹ * b, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F' (Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv F' hn') hb, ?_⟩
      group
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a * n, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F ha hn, n' * b,
        Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F' hn' hb, by group⟩

theorem key_eq_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', key t = key t' ↔ t.lam = t'.lam ∧ t.lam' = t'.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin t'.lin := by
  intro D X Y u u' t t'
  have hkey : key t = key t' ↔
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ∧ nmlOf Y u u' t = nmlOf Y u u' t' := Prod.ext_iff
  have hrow : (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ↔ t.lam = t'.lam ∧ t.lam' = t'.lam' ∧
      iotaOf Y.TR (Y.cs u) (Y.cs u') t = iotaOf Y.TR (Y.cs u) (Y.cs u') t' := by
    show rowOf Y.TR (Y.cs u) (Y.cs u') t = rowOf Y.TR (Y.cs u) (Y.cs u') t' ↔ _
    simp only [rowOf, Prod.mk.injEq, Subtype.mk.injEq]
  have hnml : nmlOf Y u u' t = nmlOf Y u u' t' ↔
      ∃ n ∈ NRat (lf D (X.Fu u)), ∃ n' ∈ NRat (lf D (X.Fu u')), t'.lin = n * t.lin * n' :=
    dcoset_eq_iff _ _ _ _
  rw [hkey, hrow, hnml]
  unfold KeyEq
  constructor
  · rintro ⟨⟨hl, hl', hi⟩, hc⟩
    exact ⟨hl, hl', hc, (Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t t' hl hl').1 hi⟩
  · rintro ⟨hl, hl', hc, hi⟩
    exact ⟨⟨hl, hl', (Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t t' hl hl').2 hi⟩, hc⟩

end GlobalTheory.Unfold.KeyIff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ValuationLtOneIffNormLtOnePadicCmCompletion
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology

namespace GlobalTheory.SlocVal

theorem tendsto_pow_map {A B : Type} [Ring A] [TopologicalSpace A] [Ring B] [TopologicalSpace B]
    (f : A →+* B) (hf : Continuous f) {x : A} (hx : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => f x ^ n) atTop (𝓝 0) := by
  have h := (hf.tendsto 0).comp hx
  rw [map_zero] at h
  simpa [Function.comp_def, map_pow] using h

theorem continuous_symm {A B : Type} [Field A] [TopologicalSpace A] [IsTopologicalRing A]
    [SigmaCompactSpace A] [Field B] [TopologicalSpace B] [IsTopologicalRing B] [BaireSpace B]
    [T2Space B] (e : A ≃+* B) (he : Continuous e) : Continuous e.symm := by
  have ho : IsOpenMap e :=
    AddMonoidHom.isOpenMap_of_sigmaCompact e.toAddEquiv.toAddMonoidHom e.surjective he
  exact e.toEquiv.continuous_symm_iff.2 ho

end GlobalTheory.SlocVal


open GlobalTheory.SlocVal in
theorem GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (g : ℕ) [Fact g.Prime] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (j : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i → Continuous j → ∀ z : s.v.adicCompletion (maximalRealSubfield L), Valued.v z < 1 ↔ ‖j.symm (i z)‖ < 1 := by
  intro L _ _ _ s g _ i j hi hj z
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion (maximalRealSubfield L) s.v
  have hj' : Continuous j.symm := continuous_symm j hj
  have hi' : Continuous i.symm := continuous_symm i hi
  have hφ : Continuous (i.trans j.symm) := hj'.comp hi
  have hψ : Continuous (i.trans j.symm).symm := hi'.comp hj
  have hz : Valued.v z < 1 ↔ ‖z‖ < 1 := (Valued.toNormedField.norm_lt_one_iff).symm
  rw [hz, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  constructor
  · intro h
    exact tendsto_pow_map (i.trans j.symm).toRingHom hφ h
  · intro h
    have := tendsto_pow_map (i.trans j.symm).symm.toRingHom hψ h
    simpa using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeEqMassOfReal
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.RankVolume

theorem definiteSpaceVolume_eq_mass_of_volumeComparison (hU : ∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) :
    ∀ D : D7, Formalism.L2.Theta.RealTied D → StandardLattice.volY0 D = StandardLattice.massI D D.R.r := fun D h =>
  have hT : StandardLattice.VolTie D := Formalism.L2.Theta.VolTieG.volTie h.vol
  StandardLattice.volume_eq_mass_at_rank D (StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D (hU D hT))
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.mass_volume_identity_of_class_decomp D hT (GlobalTheory.genusMassStd_all D)
      (GlobalTheory.DefiniteDecompObj.doubleCosets_mass D)))

end GlobalTheory.RankVolume
end

