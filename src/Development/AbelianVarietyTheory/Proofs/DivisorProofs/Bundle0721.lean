module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnRmul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal
section
open IsLocalRing GlobalTheory.Toroidal

namespace GlobalTheory.EtaleCompletionLift

section Etale

variable {O S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing S] [IsLocalRing S]
  [IsNoetherianRing S] [Algebra O S]


omit [IsNoetherianRing O] in
theorem finite_quotient (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S)
    [Module.Finite O (S ⧸ maximalIdeal S)] (n : ℕ) :
    Module.Finite O (S ⧸ (maximalIdeal O ^ (n + 1)).map (algebraMap O S)) := by
  rw [Ideal.map_pow, hm]
  have hle : maximalIdeal S ^ (n + 1) ≤ maximalIdeal S := Ideal.pow_le_self n.succ_ne_zero
  refine Module.finite_of_surjective_of_ker_le_nilradical (Ideal.Quotient.factorₐ O hle)
    (Ideal.Quotient.factor_surjective hle) ?_ (IsNoetherian.noetherian _)
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx' : x ∈ maximalIdeal S := Ideal.Quotient.eq_zero_iff_mem.1 hx
  exact mem_nilradical.2 ⟨n + 1, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hx' _⟩


omit [IsNoetherianRing O] in
theorem formallyUnramified_quotient (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S)
    [Module.Finite O (S ⧸ maximalIdeal S)] [Algebra.FormallyUnramified O (S ⧸ maximalIdeal S)] (n : ℕ) :
    Algebra.FormallyUnramified O (S ⧸ (maximalIdeal O ^ (n + 1)).map (algebraMap O S)) := by
  have := finite_quotient hm n
  set J := (maximalIdeal O ^ (n + 1)).map (algebraMap O S) with hJ
  have hle : J ≤ maximalIdeal S := by
    rw [hJ, Ideal.map_pow, hm]; exact Ideal.pow_le_self n.succ_ne_zero
  have : Nontrivial (S ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr <| ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hle
  have : IsLocalRing (S ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hmk : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal S).map (Ideal.Quotient.mk J) = maximalIdeal (S ⧸ J) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have H : (maximalIdeal O).map (algebraMap O (S ⧸ J)) = maximalIdeal (S ⧸ J) := by
    rw [← hmap, ← hm, Ideal.map_map]; rfl
  have : IsLocalHom (algebraMap O (S ⧸ J)) :=
    ((local_hom_tfae (algebraMap O (S ⧸ J))).out 3 1 rfl rfl).mp H.le
  let g : (S ⧸ maximalIdeal S) →ₐ[O] ResidueField (S ⧸ J) :=
    Ideal.Quotient.liftₐ _ ((IsScalarTower.toAlgHom O (S ⧸ J) (ResidueField (S ⧸ J))).comp (Ideal.Quotient.mkₐ O J))
      fun a ha => by
        change residue (S ⧸ J) (Ideal.Quotient.mk J a) = 0
        rw [residue_eq_zero_iff, ← hmap]
        exact Ideal.mem_map_of_mem _ ha
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨x, rfl⟩ := residue_surjective x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  have : Algebra.FormallyUnramified O (ResidueField (S ⧸ J)) := .of_surjective g hg
  have : Algebra.FormallyUnramified (ResidueField O) (ResidueField (S ⧸ J)) := .of_restrictScalars O _ _
  have : Module.Finite O (ResidueField (S ⧸ J)) := .of_surjective g.toLinearMap hg
  have : Module.Finite (ResidueField O) (ResidueField (S ⧸ J)) := .of_restrictScalars_finite O _ _
  have : Algebra.IsSeparable (ResidueField O) (ResidueField (S ⧸ J)) := Algebra.FormallyUnramified.isSeparable _ _
  exact Algebra.FormallyUnramified.of_map_maximalIdeal H

theorem etale_quotient (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S) [Module.Flat O S]
    [Module.Finite O (S ⧸ maximalIdeal S)] [Algebra.FormallyUnramified O (S ⧸ maximalIdeal S)] (n : ℕ) :
    Algebra.Etale (O ⧸ maximalIdeal O ^ (n + 1)) (S ⧸ (maximalIdeal O ^ (n + 1)).map (algebraMap O S)) := by
  have := finite_quotient hm n
  have := formallyUnramified_quotient hm n
  set I := maximalIdeal O ^ (n + 1)
  have : Module.Finite (O ⧸ I) (S ⧸ I.map (algebraMap O S)) := .of_restrictScalars_finite O _ _
  have : Algebra.FormallyUnramified (O ⧸ I) (S ⧸ I.map (algebraMap O S)) := .of_restrictScalars O _ _
  have : Algebra.FinitePresentation (O ⧸ I) (S ⧸ I.map (algebraMap O S)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.Flat (O ⧸ I) (S ⧸ I.map (algebraMap O S)) :=
    .of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
  exact .of_formallyUnramified_of_flat

theorem existsUnique_lift (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S) [Module.Flat O S]
    [Module.Finite O (S ⧸ maximalIdeal S)] [Algebra.FormallyUnramified O (S ⧸ maximalIdeal S)] (n : ℕ)
    {B : Type} [CommRing B] (χ : O →+* B) (hχ : ∀ x ∈ maximalIdeal O ^ (n + 1), χ x = 0) (K : Ideal B)
    (hK : IsNilpotent K) (g : S →+* B ⧸ K) (hg : g.comp (algebraMap O S) = (Ideal.Quotient.mk K).comp χ) :
    ∃! F : S →+* B, F.comp (algebraMap O S) = χ ∧ (Ideal.Quotient.mk K).comp F = g := by
  have := etale_quotient hm n
  set I := maximalIdeal O ^ (n + 1)
  letI : Algebra (O ⧸ I) B := (Ideal.Quotient.lift I χ hχ).toAlgebra
  have desc : ∀ {C : Type} [CommRing C] [Algebra (O ⧸ I) C] (f : S →+* C),
      (∀ x, f (algebraMap O S x) = algebraMap (O ⧸ I) C (Ideal.Quotient.mk I x)) →
      ∃ f' : (S ⧸ I.map (algebraMap O S)) →ₐ[O ⧸ I] C, ∀ x, f' (Ideal.Quotient.mk _ x) = f x := by
    intro C _ _ f hf
    have h0 : I.map (algebraMap O S) ≤ RingHom.ker f := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change f (algebraMap O S x) = 0
      rw [hf, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    refine ⟨⟨Ideal.Quotient.lift _ f fun a ha => h0 ha, fun r => ?_⟩, fun x => rfl⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact hf r
  obtain ⟨g', hg'⟩ := desc g fun x => congr($hg x)
  let F := Algebra.FormallySmooth.lift K hK g'
  refine ⟨F.toRingHom.comp (Ideal.Quotient.mk _), ⟨RingHom.ext fun x => ?_, RingHom.ext fun x => ?_⟩, ?_⟩
  · exact F.commutes (Ideal.Quotient.mk I x)
  · exact (Algebra.FormallySmooth.mk_lift K hK g' _).trans (hg' x)
  · rintro G ⟨h1, h2⟩
    obtain ⟨G', hG'⟩ := desc G fun x => congr($h1 x)
    have : G' = F := Algebra.FormallyUnramified.ext K hK fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Algebra.FormallySmooth.mk_lift K hK g', hg', hG']
      exact congr($h2 x)
    ext x
    rw [← hG', this]
    rfl

theorem existsUnique_lift_of_surjective (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S)
    [Module.Flat O S] [Module.Finite O (S ⧸ maximalIdeal S)] [Algebra.FormallyUnramified O (S ⧸ maximalIdeal S)]
    (n : ℕ) {B C : Type} [CommRing B] [CommRing C] (χ : O →+* B) (hχ : ∀ x ∈ maximalIdeal O ^ (n + 1), χ x = 0)
    (w : B →+* C) (hw : Function.Surjective w) (hK : IsNilpotent (RingHom.ker w)) (g : S →+* C)
    (hg : g.comp (algebraMap O S) = w.comp χ) :
    ∃! F : S →+* B, F.comp (algebraMap O S) = χ ∧ w.comp F = g := by
  let e := RingHom.quotientKerEquivOfSurjective hw
  have := existsUnique_lift hm n χ hχ _ hK (e.symm.toRingHom.comp g) (by
    ext x
    exact e.symm_apply_eq.2 congr($hg x))
  refine (existsUnique_congr fun F => and_congr Iff.rfl ?_).1 this
  simp only [RingHom.ext_iff]
  exact forall_congr' fun x => e.eq_symm_apply

end Etale

theorem existsUnique_lift_of_isEtaleCompletion {O S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {φ : O →+* S} (h : IsEtaleCompletion φ)
    (hun : ((residue S).comp φ).FormallyUnramified)
    (n : ℕ) {B C : Type} [CommRing B] [CommRing C] (χ : O →+* B) (hχ : ∀ x ∈ maximalIdeal O ^ (n + 1), χ x = 0)
    (w : B →+* C) (hw : Function.Surjective w) (hK : IsNilpotent (RingHom.ker w)) (g : S →+* C)
    (hg : g.comp φ = w.comp χ) :
    ∃! F : S →+* B, F.comp φ = χ ∧ w.comp F = g := by
  obtain ⟨hfl, hm, hfin⟩ := h
  letI := φ.toAlgebra
  have : Module.Flat O S := hfl
  have : Module.Finite O (S ⧸ maximalIdeal S) := RingHom.finite_algebraMap.1 hfin
  have : Algebra.FormallyUnramified O (S ⧸ maximalIdeal S) := RingHom.formallyUnramified_algebraMap.1 hun
  exact existsUnique_lift_of_surjective hm n χ hχ w hw hK g hg

theorem isNilpotent_ker {E C : Type} [CommRing E] [CommRing C] {I : Ideal E} {v : E →+* C} (hv : RingHom.ker v = I)
    (n : ℕ) (w : E ⧸ I ^ (n + 1) →+* C) (hw : ∀ x, w (Ideal.Quotient.mk _ x) = v x) :
    IsNilpotent (RingHom.ker w) := by
  have : RingHom.ker w ≤ I.map (Ideal.Quotient.mk (I ^ (n + 1))) := fun x hx => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Ideal.mem_map_of_mem _ ?_
    rw [← hv, RingHom.mem_ker, ← hw]
    exact hx
  refine ⟨n + 1, le_bot_iff.1 ((Ideal.pow_right_mono this _).trans ?_)⟩
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem exists_extension_of_surjective {O S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {φ : O →+* S} (het : IsEtaleCompletion φ)
    (hun : ((residue S).comp φ).FormallyUnramified) {E C : Type} [CommRing E] [CommRing C] (m : Ideal E)
    [IsAdicComplete m E] (ψ : O →+* E) (h1 : (maximalIdeal O).map ψ ≤ m) (v : E →+* C) (hs : Function.Surjective v)
    (hv : RingHom.ker v = m) (u : S →+* C) (hc : u.comp φ = v.comp ψ) :
    ∃ b : S →+* E, b.comp φ = ψ ∧ v.comp b = u := by
  have hle : ∀ n : ℕ, m ^ (n + 1) ≤ RingHom.ker v := fun n => (Ideal.pow_le_self n.succ_ne_zero).trans hv.ge
  obtain ⟨w, hw⟩ : ∃ w : ∀ n : ℕ, E ⧸ m ^ (n + 1) →+* C, ∀ n x, w n (Ideal.Quotient.mk _ x) = v x :=
    ⟨fun n => Ideal.Quotient.lift _ v fun a ha => hle n ha, fun n x => Ideal.Quotient.lift_mk _ _ _⟩
  have hws : ∀ n, Function.Surjective (w n) := fun n y => by
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨_, hw n x⟩
  have key : ∀ n, ∃! F : S →+* E ⧸ m ^ (n + 1),
      F.comp φ = (Ideal.Quotient.mk _).comp ψ ∧ (w n).comp F = u := fun n => by
    refine existsUnique_lift_of_isEtaleCompletion het hun n _ (fun x hx => ?_) _ (hws n)
      (isNilpotent_ker hv n _ (hw n)) _ ?_
    · rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      refine Ideal.pow_right_mono h1 _ ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hx
    · ext x
      rw [hc, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, hw]
  choose F hF hU using key
  have hF1 : ∀ n x, F n (φ x) = Ideal.Quotient.mk _ (ψ x) := fun n x => RingHom.congr_fun (hF n).1 x
  have hF2 : ∀ n x, w n (F n x) = u x := fun n x => RingHom.congr_fun (hF n).2 x
  have ha : StrictMono (fun n : ℕ => n + 1) := strictMono_id.add_const 1
  have hcomp : ∀ {k : ℕ}, (Ideal.Quotient.factorPow m (ha.monotone k.le_succ)).comp (F (k + 1)) = F k := by
    intro k
    refine hU k _ ⟨RingHom.ext fun x => ?_, RingHom.ext fun x => ?_⟩
    · simp only [RingHom.comp_apply, hF1, Ideal.Quotient.factor_mk]
    · rw [← hF2 (k + 1), RingHom.comp_apply, RingHom.comp_apply]
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (F (k + 1) x)
      rw [← hy, hw]
      exact (congrArg (w k) (Ideal.Quotient.factor_mk _ y)).trans (hw k y)
  obtain ⟨b, hb⟩ : ∃ b : S →+* E, ∀ n x, Ideal.Quotient.mk (m ^ (n + 1)) (b x) = F n x :=
    ⟨_, fun n x => IsAdicComplete.StrictMono.mk_liftRingHom m ha F hcomp x⟩
  refine ⟨b, ?_, ?_⟩
  · apply DFunLike.coe_injective
    apply IsHausdorff.StrictMono.funext' m ha
    intro n x
    exact (hb n _).trans (hF1 n x)
  · ext x
    rw [RingHom.comp_apply, ← hw 0, hb, hF2]

theorem exists_extension : ∀ (O R' E Ω : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R']
    [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [Field Ω] (φ' : O →+* R') (ψ : O →+* E)
    (u' : R' →+* Ω) (v : E →+* Ω), IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified →
    IsAdicComplete (maximalIdeal E) E → IsLocalHom ψ → RingHom.ker u' = maximalIdeal R' →
    RingHom.ker v = maximalIdeal E → v.comp ψ = u'.comp φ' → (∀ r : R', u' r ∈ v.range) →
    ∃ b : R' →+* E, b.comp φ' = ψ ∧ v.comp b = u' := by
  intro O R' E Ω _ _ _ _ _ _ _ _ _ φ' ψ u' v het hun hE hψ _ hv hc hr
  obtain ⟨b, h1, h2⟩ := exists_extension_of_surjective het hun (maximalIdeal E) ψ
    (((local_hom_tfae ψ).out 1 3 rfl rfl).mp hψ) v.rangeRestrict v.rangeRestrict_surjective
    (v.ker_rangeRestrict.trans hv) (u'.codRestrict v.range hr)
    (RingHom.ext fun x => Subtype.ext (RingHom.congr_fun hc x).symm)
  exact ⟨b, h1, RingHom.ext fun x => congrArg Subtype.val (RingHom.congr_fun h2 x)⟩

end GlobalTheory.EtaleCompletionLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarIntegralEqUnitriangularChart
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal Matrix

namespace GlobalTheory.FlagQuotHaar

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def baseGL (X : Data E r) (τ : X.Ψ) : GL (Fin r) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (mat (baseFr X) τ) (PeterssonCompare.det_baseFr X τ)

theorem val_baseGL (X : Data E r) (τ : X.Ψ) : (baseGL X τ : Matrix (Fin r) (Fin r) ℂ) = mat (baseFr X) τ := rfl


omit [NumberField E] [IsCMField E] in
theorem gram_mul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (A g : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (A * g) = gᵀ * gram τ G A * g.map (starRingEnd ℂ) := by
  rw [UnitaryFrames.gram_eq_mul, UnitaryFrames.gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]


omit [NumberField E] [IsCMField E] in
theorem isometry_iff_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (n : Matrix (Fin r) (Fin r) ℂ)
    (P : GL (Fin r) ℂ) :
    (∀ u w, hermC τ G (n *ᵥ u) (n *ᵥ w) = hermC τ G u w) ↔
      gram τ G (n * (P : Matrix (Fin r) (Fin r) ℂ)) = gram τ G P := by
  constructor
  · intro h
    ext a b
    simp only [gram, Matrix.of_apply, UnitaryFrames.col_mul', h]
  · intro h u w
    obtain ⟨u', rfl⟩ : ∃ u', u = (P : Matrix (Fin r) (Fin r) ℂ) *ᵥ u' :=
      ⟨((P⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ u, by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
    obtain ⟨w', rfl⟩ : ∃ w', w = (P : Matrix (Fin r) (Fin r) ℂ) *ᵥ w' :=
      ⟨((P⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w, by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, UnitaryFrames.hermC_mulVec, UnitaryFrames.hermC_mulVec, h]

def toIso (X : Data E r) (g : RealGrp X) : UnitaryFrames.unitarySubgroup X :=
  ⟨fun τ => baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹, by
    intro τ
    refine (isometry_iff_gram τ.1 X.Gm _ (baseGL X τ)).2 ?_
    rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul, gram_mul_right, val_baseGL, baseFr_mem X τ]
    exact (g τ).2⟩

def ofIso (X : Data E r) (h : UnitaryFrames.unitarySubgroup X) : RealGrp X :=
  fun τ => ⟨(baseGL X τ)⁻¹ * (h : X.Ψ → GL (Fin r) ℂ) τ * baseGL X τ, by
    have hu : gram τ.1 X.Gm (((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) *
        (baseGL X τ : Matrix (Fin r) (Fin r) ℂ)) = gram τ.1 X.Gm (baseGL X τ) :=
      (isometry_iff_gram τ.1 X.Gm _ (baseGL X τ)).1 (h.2 τ)
    have e : ((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * (baseGL X τ : Matrix (Fin r) (Fin r) ℂ) =
        (baseGL X τ : Matrix (Fin r) (Fin r) ℂ) *
          (((baseGL X τ)⁻¹ * (h : X.Ψ → GL (Fin r) ℂ) τ * baseGL X τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [e, gram_mul_right, val_baseGL, baseFr_mem X τ] at hu
    exact hu⟩

def isoEquiv (X : Data E r) : RealGrp X ≃ₜ* UnitaryFrames.unitarySubgroup X where
  toFun := toIso X
  invFun := ofIso X
  left_inv g := by
    funext τ
    apply Subtype.ext
    show (baseGL X τ)⁻¹ * (baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹) * baseGL X τ = _
    group
  right_inv h := by
    apply Subtype.ext
    funext τ
    show baseGL X τ * ((baseGL X τ)⁻¹ * (h : X.Ψ → GL (Fin r) ℂ) τ * baseGL X τ) * (baseGL X τ)⁻¹ = _
    group
  map_mul' g g' := by
    apply Subtype.ext
    funext τ
    show baseGL X τ * (((g * g') τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹ =
      (baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹) *
        (baseGL X τ * ((g' τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹)
    simp only [Pi.mul_apply, Subgroup.coe_mul]
    group
  continuous_toFun := by
    refine continuous_induced_rng.2 (continuous_pi fun τ => ?_)
    exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply τ))).mul continuous_const
  continuous_invFun := by
    refine continuous_pi fun τ => continuous_induced_rng.2 ?_
    exact (continuous_const.mul ((continuous_apply τ).comp continuous_subtype_val)).mul continuous_const

theorem frameOf_eq_lmulC (X : Data E r) (g : RealGrp X) :
    frameOf X g = X.lmulC (fun τ => (((toIso X g : UnitaryFrames.unitarySubgroup X) : X.Ψ → GL (Fin r) ℂ) τ :
      Matrix (Fin r) (Fin r) ℂ)) (baseFr X) := by
  funext τ
  have key : mat (frameOf X g) τ = mat (X.lmulC (fun τ => (((toIso X g : UnitaryFrames.unitarySubgroup X) :
      X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) (baseFr X)) τ := by
    rw [PeterssonCompare.mat_frameOf, show ∀ (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r),
    mat (X.lmulC n x) τ = n τ * mat x τ from fun _ _ => rfl, ← val_baseGL]
    show _ = ((baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹ : GL (Fin r) ℂ) :
    Matrix (Fin r) (Fin r) ℂ) * _
    rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  exact key

theorem muF_univ_ne_zero (X : Data E r) {x0 : Frame X.Ψ r} (h : IsOrth X x0) : muF X x0 Set.univ ≠ 0 := by
  have hO := OntoB.isOpen_OmF X x0
  unfold muF
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  intro h0
  have hm : AEMeasurable (fun z => ENNReal.ofReal (densF X x0 z)) (volume.restrict (OmF X x0)) :=
    (OntoB.densF_continuousOn.aemeasurable hO.measurableSet).ennreal_ofReal
  rw [lintegral_eq_zero_iff' hm] at h0
  have h1 : ∀ᵐ z ∂(volume.restrict (OmF X x0)), False := by
    filter_upwards [h0, ae_restrict_mem hO.measurableSet] with z hz hz'
    have := OntoB.densF_pos hz'
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hz
    linarith
  rw [ae_iff] at h1
  simp only [not_false_eq_true, Set.setOf_true, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter] at h1
  exact (hO.measure_pos volume ⟨0, IW.zero_mem_OmF X x0 h⟩).ne' h1

theorem exists_haarChart (X : Data E r) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ HaarChart X c := by
  classical
  set H := UnitaryFrames.unitarySubgroup X with hHdef
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  have hHm : ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ) := fun _ => Iff.rfl
  obtain ⟨hLC, hSC, -⟩ := UnitaryFrames.unitary_group_frames.2 r X H hHm
  haveI := hLC
  haveI := hSC
  have hx0 : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
  obtain ⟨ν, hνl, hνf, hν⟩ := UnitaryInvMeasure.invMeas FrameMeasureClosed.measure_statements.2.1
    GramSchmidtCont.exists_continuous_gramSchmidt isOrth_rmul_iff_unitary_diagonal
    (SatFin.muF_sat_lt_top FrameMeasureClosed.measure_statements.2.1)
    UnitaryFrames.unitary_group_frames.2 r X H hHm (baseFr X) hx0
  haveI := hνl
  haveI := hνf
  haveI : (haarR X).IsHaarMeasure := by unfold haarR; infer_instance
  set e := isoEquiv X
  set μ : Measure H := (haarR X).map e with hμdef
  haveI : μ.IsHaarMeasure := e.isHaarMeasure_map (haarR X)
  have hs := Measure.isMulLeftInvariant_eq_smul ν μ
  set s := ν.haarScalarFactor μ
  set L : H → Frame X.Ψ r := fun h =>
    X.lmulC (fun τ => ((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) (baseFr X)

  have hR : ∀ F : H → ℝ≥0∞, ∫⁻ g, F (e g) ∂haarR X = ∫⁻ h, F h ∂μ := by
    intro F
    have := lintegral_map_equiv F (e.toHomeomorph.toMeasurableEquiv) (μ := haarR X)
    exact this.symm
  have hs0 : s ≠ 0 := by
    intro h0
    have h1 := hν (fun _ => 1) measurable_const (fun _ _ _ _ => rfl)
    simp only [lintegral_const, one_mul] at h1
    rw [hs, h0, zero_smul, Measure.coe_zero, Pi.zero_apply] at h1
    exact muF_univ_ne_zero X hx0 h1.symm
  refine ⟨((s : ℝ≥0∞))⁻¹, ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top,
    ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 hs0), fun φ hφ hφb => ?_⟩
  have h1 := hν φ hφ hφb
  rw [hs, lintegral_smul_measure] at h1
  have h2 : ∫⁻ g, φ (frameOf X g) ∂haarR X = ∫⁻ h, φ (L h) ∂μ := by
    rw [← hR]
    refine lintegral_congr fun g => ?_
    rw [frameOf_eq_lmulC]
    rfl
  rw [h2, ← h1, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hs0)
    ENNReal.coe_ne_top, one_mul]

end

end GlobalTheory.FlagQuotHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntVVariableChange
section
open WeierstrassCurve

namespace GlobalTheory.CMModel

theorem exists_intV_variableChange (W : WeierstrassCurve ℂ) [W.IsElliptic] (V : ValuationSubring ℂ)
    (u : ℂˣ) (hj : W.j ∈ V) (hu : V.valuation (u : ℂ) ^ 12 = V.valuation W.Δ) :
    ∃ r s t : ℂ, IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • W) := by
  have : IsIntegrallyClosedIn V ℂ := (isIntegrallyClosed_iff_isIntegrallyClosedIn ℂ).1 inferInstance
  have ht : HasRationalTorsion W ℂ 12 := by
    intro x y h hn
    exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  obtain ⟨C, W₀, e, h₀⟩ := exists_integral_model V (L := ℂ) (W := W) ⟨⟨W.j, hj⟩, rfl⟩ ht
  have hΔ : ((C.u⁻¹ : ℂˣ) : ℂ) ^ 12 * W.Δ = 1 := by
    rw [← variableChange_Δ, e, WeierstrassCurve.baseChange, map_Δ, h₀, map_one]
  have hCu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  have hu0 : (u : ℂ) ≠ 0 := u.ne_zero
  have hΔ' : W.Δ = (C.u : ℂ) ^ 12 := by
    rw [Units.val_inv_eq_inv_val] at hΔ
    field_simp at hΔ
    exact hΔ
  have hv : V.valuation (u : ℂ) = V.valuation (C.u : ℂ) := by
    rw [hΔ', map_pow] at hu
    exact (pow_left_inj₀ zero_le' zero_le' (by norm_num)).1 hu
  have hw : (C.u : ℂ) / u ∈ V := by
    rw [← V.valuation_le_one_iff, map_div₀, hv, div_self]
    exact (map_ne_zero _).2 hCu
  have h1 : (C • W).a₁ ∈ V := by rw [e]; exact W₀.a₁.2
  have h2 : (C • W).a₂ ∈ V := by rw [e]; exact W₀.a₂.2
  have h3 : (C • W).a₃ ∈ V := by rw [e]; exact W₀.a₃.2
  have h4 : (C • W).a₄ ∈ V := by rw [e]; exact W₀.a₄.2
  have h6 : (C • W).a₆ ∈ V := by rw [e]; exact W₀.a₆.2
  refine ⟨C.r, C.s, C.t, ?_, ?_, ?_, ?_, ?_⟩
  · convert V.mul_mem _ _ hw h1 using 1
    simp only [variableChange_a₁, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 2) h2 using 1
    simp only [variableChange_a₂, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 3) h3 using 1
    simp only [variableChange_a₃, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 4) h4 using 1
    simp only [variableChange_a₄, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 6) h6 using 1
    simp only [variableChange_a₆, Units.val_inv_eq_inv_val]; field_simp

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseConjMemClosureOfIsCompact
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory

theorem exists_inverse_conj_mem_closure_of_isCompact :
    ∀ (X : Type) [Monoid X] [TopologicalSpace X] [ContinuousMul X] [T2Space X] (H C : Set X),
      IsCompact C → ∀ g : X, (∀ W ∈ 𝓝 g, ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧
        ∃ w ∈ W, c * w * c' ∈ H) →
      ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ c * g * c' ∈ closure H := by
  intro X _ _ _ _ H C hC g hW
  let K : Set (X × X) := (C ×ˢ C) ∩ {p | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1}
  have hK : IsCompact K := by
    refine (hC.prod hC).inter_right ?_
    exact (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter
      (isClosed_eq (continuous_snd.mul continuous_fst) continuous_const)
  by_contra hne
  push_neg at hne
  have hcont : Continuous fun z : X × (X × X) => z.2.1 * z.1 * z.2.2 :=
    ((continuous_snd.fst).mul continuous_fst).mul continuous_snd.snd
  have hP : ∀ y ∈ K, ∀ᶠ z : X × (X × X) in 𝓝 (g, y), z.2.1 * z.1 * z.2.2 ∈ (closure H)ᶜ := by
    intro y hy
    apply hcont.continuousAt.preimage_mem_nhds
    apply isClosed_closure.isOpen_compl.mem_nhds
    exact hne y.1 hy.1.1 y.2 hy.1.2 hy.2.1 hy.2.2
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := g)
    (P := fun w (y : X × X) => y.1 * w * y.2 ∈ (closure H)ᶜ) hP
  obtain ⟨c, hc, c', hc', h1, h2, w, hw, hH⟩ := hW _ hev
  exact hw (c, c') ⟨⟨hc, hc'⟩, h1, h2⟩ (subset_closure hH)

end GlobalTheory
end

