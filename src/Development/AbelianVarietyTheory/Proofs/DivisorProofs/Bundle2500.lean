module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperThetaValueImageEqImageValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep
open GlobalTheory.Points


open GlobalTheory.ZH.RatModel in
theorem Tower.valF_app_p {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    {U : X₁.M.Z.Opens} (hU : (U : Set X₁.M.Z).Nonempty) (a : Γ(X₁.M.Z, U)) :
    valF 𝔗.X₂.M.pt (𝔗.p ⁻¹ᵁ U) (𝔗.p.app U a) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (valF X₁.M.pt U a) := by
  refine (valR_comp 𝔗.X₂.M.pt 𝔗.p U a).symm.trans ?_
  rw [𝔗.p_pt]
  exact valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt hU) a

theorem Tower.stalkHom_stalkMap_p {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    (z₂ : 𝔗.X₂.M.Z) (x : X₁.M.Z.presheaf.stalk (𝔗.p z₂)) :
    𝔗.X₂.M.stalkHom z₂ (𝔗.p.stalkMap z₂ x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) := by
  obtain ⟨U, hz, f, rfl⟩ := X₁.M.Z.presheaf.germ_exist x
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ hz f]
  exact (RatModel.stalkHom_germ (M := 𝔗.X₂.M) (U := 𝔗.p ⁻¹ᵁ U) hz _).trans (𝔗.valF_app_p ⟨_, hz⟩ f)

theorem Tower.val_comp_p {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    {K : Type} [Field K] (y : Sp K ⟶ 𝔗.X₂.M.Z) (w : Sp K) {x : X₁.Ω₁} (hx : x ∈ X₁.M.O (𝔗.p (y w))) :
    X₁.M.val (y ≫ 𝔗.p) x = 𝔗.X₂.M.val y (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ x) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ (𝔗.p ⁻¹ᵁ U : 𝔗.X₂.M.Z.Opens) := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [← 𝔗.valF_app_p ⟨_, hz⟩ a, RatModel.val_valF h1,
    RatModel.val_valF (U := U) (by rintro _ ⟨w', rfl⟩; exact h1 ⟨w', rfl⟩)]
  exact valR_comp y 𝔗.p U a

theorem RatModel.val_spMap_comp_field {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {K K' : Type} [Field K]
    [Field K'] (σ : K →+* K') (y : Sp K ⟶ M.Z) (w : Sp K) {x : Ω} (hx : x ∈ M.O (y w)) :
    M.val (spMap σ ≫ y) x = σ (M.val y x) := by
  obtain ⟨U, g, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ U := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [RatModel.val_valF h1, RatModel.val_valF (by rintro _ ⟨w', rfl⟩; exact h1 ⟨_, rfl⟩)]
  exact valR_spMap_comp σ y U ((top_le_preimage_iff _ _).2 h1) g

theorem Tower.val_om_ext : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → 𝔗.Ext ev io ev₂ → RegAt X₁ z₁ ev → ∀ a : X₁.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.om a) = f (X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) := by
  intro g n F W Z i X₁ act 𝔗 z₁ z₂ hz V V' _ _ _ _ ev io ev₂ f hf hio hext hreg a
  subst hz
  have e1 : ev₂.comp (𝔗.p.stalkMap z₂).hom = io.comp ev :=
    RingHom.ext fun x => hext.2 x _ (𝔗.stalkHom_stalkMap_p z₂ x)
  have e2 : jK V' ≫ spMap io = spMap f ≫ jK V := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext v
    exact (hf v).symm
  have h1 : (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) ≫ 𝔗.p =
      spMap f ≫ (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) := by
    have e3 : spMap ev₂ ≫ Spec.map (𝔗.p.stalkMap z₂) = spMap io ≫ spMap ev := by
      show Spec.map (CommRingCat.ofHom ev₂) ≫ Spec.map (CommRingCat.ofHom (𝔗.p.stalkMap z₂).hom) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e1, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc (spMap ev₂), e3,
      Category.assoc, ← Category.assoc (jK V'), e2]
    simp only [Category.assoc]
  have hmem := hreg a a.2
  have hp : 𝔗.p ((jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (closedPoint (FractionRing V'))) =
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) (closedPoint (FractionRing V)) := by
    have e := congrArg (fun q : Sp (FractionRing V') ⟶ X₁.M.Z => q (closedPoint (FractionRing V'))) h1
    refine e.trans ?_
    show (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) ((spMap f) (closedPoint (FractionRing V'))) = _
    rw [Subsingleton.elim ((spMap f) (closedPoint (FractionRing V'))) (closedPoint (FractionRing V))]
  rw [𝔗.om_eq, ← 𝔗.val_comp_p (K := FractionRing V') _ (closedPoint (FractionRing V')) (hp ▸ hmem), h1,
    RatModel.val_spMap_comp_field (K := FractionRing V) f _ (closedPoint (FractionRing V)) hmem]

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedLatticeSumDerivativesEqEisensteinJets
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

namespace GlobalTheory.HilbFam

theorem iterD_defSum_eq_jet : EisExp → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (s N : ℕ) (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), 2 ≤ Module.finrank ℚ (FR E) → 1 ≤ s → 0 < N → HasLevel N L → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsDefSum φ (2 * s) Λ g → (∀ i, u.count i = κ i) → iterD u g 0 = (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * jet (2 * s) L (fun j ↦ κ (e.symm j)) τ 1 (starRingEnd ℂ (τ : ℂ) - τ) := by
  intro hE E _ _ _ I _ _ φ e θ τ Λ L n s N g κ u hf hs hN hL hφ hθ hn hLΛ hg hu
  have hI : Nonempty I := by
    obtain ⟨σ⟩ : Nonempty (FR E →+* ℂ) := by
      rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]; omega
    exact ⟨e.symm (NumberField.ComplexEmbedding.IsReal.embedding
      (IsTotallyReal.complexEmbedding_isReal σ))⟩
  set W : (Emb (FR E) → ℂ) → ℂ := fun w ↦ (cK (FR E) (2 * s) : ℂ) *
    gval (2 * s) L (fun j ↦ (τ : ℂ) + w j * (1 * (τ : ℂ) + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + w j * 1) with hW
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : g =ᶠ[nhds 0] fun z ↦ (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * W (fun j ↦ z (e.symm j)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : I → ℂ) one_pos] with z hz
    have hzp : z ∈ polydisc I := fun i ↦ by
      have := norm_le_pi_norm z i
      rw [Metric.mem_ball, dist_zero_right] at hz
      exact lt_of_le_of_lt this hz
    obtain ⟨G, hG, hgz⟩ := hg z hzp
    have hv := _root_.GlobalTheory.HilbFam.BrVal.isGVal_of_isEisValue E I φ e θ τ Λ L n (2 * s) z G hI ⟨s, two_mul s⟩ hφ hθ hn hLΛ hG
    have hu' := GlobalTheory.HilbFam.gval_eq_of_isGVal (FR E) (2 * s) L _ _ _ hv
    simp only [hW]
    rw [hu', hgz]
    have : (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) = (cK (FR E) (2 * s) : ℂ) := rfl
    rw [this, inv_pow, ← pow_mul, mul_comm (Module.finrank ℚ (FR E)) (2 * s)]
    have h1 : (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) ≠ 0 := pow_ne_zero _ hn0
    rw [mul_left_comm, mul_inv_cancel_left₀ h1]
  rw [GlobalTheory.HilbFam.iterD_eq_of_eventuallyEq I u g _ 0 key, GlobalTheory.HilbFam.iterD_const_mul_reindex I (Emb (FR E)) e u W _ 0]
  congr 1
  have hc : ∀ j, (u.map e).count j = κ (e.symm j) := fun j ↦ by
    rw [← hu (e.symm j)]
    conv_lhs => rw [← e.apply_symm_apply j]
    convert List.count_map_of_injective u e e.injective (e.symm j)
  have := _root_.GlobalTheory.HilbFam.iterD_eq_jet_of_count hE (FR E) hf s N L hs hN hL τ 1 (starRingEnd ℂ (τ : ℂ) - τ) (fun j ↦ κ (e.symm j)) (u.map e) τ.im_pos hc
  exact this

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationQuotientPointsRationalFiniteExtensio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem qkPt_rational_of_pull : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ → IsLocalHom i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p := by
  intro R₁ _ _ _ hR D₁ n hn
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hG := hL.globalFns
  have hB₁ := D₁.tau_bimult
  have := hR.2
  have : CharZero (Kb R₁) := (RingHom.charZero_iff (algebraMap (FractionRing R₁) (Kb R₁)).injective).1 inferInstance
  obtain ⟨M, hM, H⟩ := GlobalTheory.QkNumberField.exists_finite_qk (D := D₁.toPre) (L := Kb R₁) hL hB₁ (N := n)
    (Nat.cast_ne_zero.2 (by omega))
  refine ⟨M, hM, ?_⟩
  intro R₂ _ _ _ i₁₂ e hfin _ he D₂ ⟨hD⟩ p
  have hB₂ := D₂.tau_bimult
  have hi : Function.Injective i₁₂ := hfin.2.1
  letI : Algebra (FractionRing R₁) (FractionRing R₂) := (fracMap hi).toAlgebra
  have he' : e.comp (algebraMap (FractionRing R₁) M) = algebraMap (FractionRing R₁) (FractionRing R₂) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R₁) (RingHom.ext fun r => (he r).trans (fracMap_algebraMap hi r).symm)
  letI : Algebra (FractionRing R₁) (Kb R₂) := ((algebraMap (FractionRing R₂) (Kb R₂)).comp (fracMap hi)).toAlgebra
  have cK : Compat i₁₂ (Kb R₂) := fun r => congrArg (algebraMap (FractionRing R₂) (Kb R₂)) (fracMap_algebraMap hi r)
  have cF : Compat i₁₂ (FractionRing R₂) := fracMap_algebraMap hi
  letI : Algebra M (Kb R₂) := ((algebraMap (FractionRing R₂) (Kb R₂)).comp e).toAlgebra
  haveI : Module.IsTorsionFree M (Kb R₂) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree M (Kb R₁) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Algebra.IsAlgebraic M (Kb R₁) := Algebra.IsAlgebraic.tower_top (K := FractionRing R₁) M
  let σ' : Kb R₁ →ₐ[M] Kb R₂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hσ' : ∀ m : M, σ' (m : Kb R₁) = algebraMap (FractionRing R₂) (Kb R₂) (e m) := fun m => σ'.commutes m
  let σ : Kb R₁ →ₐ[FractionRing R₁] Kb R₂ := ⟨σ'.toRingHom, fun x => by
    show σ' (algebraMap (FractionRing R₁) (Kb R₁) x) = _
    exact (hσ' (algebraMap (FractionRing R₁) M x)).trans (congrArg (algebraMap (FractionRing R₂) (Kb R₂)) (RingHom.congr_fun he' x))⟩
  have key : σ.toRingHom.comp M.val.toRingHom = (algebraMap (FractionRing R₂) (Kb R₂)).comp e :=
    RingHom.ext fun m => hσ' m
  obtain ⟨q, rfl⟩ := pullQk_surjective hD hG cK hB₁ hB₂ p
  obtain ⟨q₀, hq₀⟩ := GlobalTheory.LabTrans.exists_of_ext hB₁ σ hn q
  obtain ⟨z, rfl⟩ := H n dvd_rfl q₀
  let z' : QkPt D₁.toPre (FractionRing R₂) n := qkExt hB₁ e he' z
  let p₀ := pullQk hD hG cF hB₁ hB₂ z'
  let p₁ := qkExt hB₂ (algebraMap (FractionRing R₂) (Kb R₂)) (RingHom.comp_id _) p₀
  have hp₁ : QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ := (qkExt_iff hB₂ _ _ _ _).2 rfl
  have hf₂ : (algebraMap (FractionRing R₂) (Kb R₂)).comp (algebraMap (FractionRing R₁) (FractionRing R₂)) =
      algebraMap (FractionRing R₁) (Kb R₂) := rfl
  let w := qkExt hB₁ (algebraMap (FractionRing R₂) (Kb R₂)) hf₂ z'
  have hw : QkExt (algebraMap (FractionRing R₂) (Kb R₂)) z' w := (qkExt_iff hB₁ _ _ _ _).2 rfl
  have hz' : QkExt e z z' := (qkExt_iff hB₁ _ _ _ _).2 rfl
  have hz : QkExt M.val.toRingHom z (qkExt hB₁ M.val.toRingHom (GlobalTheory.QkNumberField.val_comp M) z) :=
    (qkExt_iff hB₁ _ _ _ _).2 rfl
  have t₁ := GlobalTheory.LabTrans.qkExt_trans hz hq₀
  have t₂ := GlobalTheory.LabTrans.qkExt_trans hz' hw
  rw [← key] at t₂
  have hqw : q = w := GlobalTheory.QkClosure.qkExt_unique (σ.toRingHom.comp M.val.toRingHom) (σ.comp_algebraMap ▸ rfl) t₁ t₂
  refine ⟨p₀, p₁, hp₁, ?_⟩
  have e₁ : p₁ = pullQk hD hG cK hB₁ hB₂ q := by
    rw [eq_pullQk_iff]
    refine ⟨?_, ?_⟩
    · rw [hqw]; rfl
    · rw [hqw]
      exact isPullGtF_ext hD cK _ (RingHom.comp_id _) (isPullGtF_pullGt hD hG cF z'.g) hw hp₁
  rw [e₁]
  exact qk_equiv_refl hB₂ _

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneFamilyTermEqPsiThetaValueCharacter
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.IntTerm


open GlobalTheory.Poinc.ThetaOne in
theorem coef_eq_theta_value : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ s : Fam D (FractionRing V) 1, ∃ κ₀ : FractionRing V, ∀ (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b), w.IsGen → ∀ (mu : D.X) (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing V) z (coef s g' w mu) * (rigV D (TF (R := V) (FractionRing V)).hom z J).val * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val = GlobalTheory.UT.cst (FractionRing V) z κ₀ * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s mu) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val := by
  intro V _ _ D θ hθ s
  obtain ⟨κ₀, hκ, -⟩ := existsUnique_scalar D θ hθ (FractionRing V) s
  refine ⟨κ₀, fun g' w hw mu z J hJ => ?_⟩
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  let ρ : TF (R := V) (FractionRing V) ⟶ DegPre.BF D (FractionRing V) := lift (𝟙 _) g'.b
  have hρ₁ : ρ ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have hρ₂ : ρ ≫ DegPre.prB D (FractionRing V) = g'.b := lift_snd _ _

  have s0 : ∀ (r : (TF (R := V) (FractionRing V)).left ⟶ (DegPre.BF D (FractionRing V)).left),
      sval (s.s 0) r z J = GlobalTheory.FieldBaseChange.constVal (r ≫ GlobalTheory.FieldBaseChange.famBase D (FractionRing V)) z κ₀ *
        sval θ (r ≫ (DegPre.prB D (FractionRing V)).left) z J := by
    intro r
    have h1 : (GlobalTheory.FieldBaseChange.famProj D (FractionRing V) 1 0 s) = κ₀ • termF D (FractionRing V) 1 0 θ := hκ
    have h2 := congrArg (fun t : GlobalTheory.FieldBaseChange.FamTerm D (FractionRing V) 1 0 => sval (L := D.P.L) t r z J) h1
    refine h2.trans ?_
    rw [GlobalTheory.FieldBaseChange.sval_smul' hJ]
    congr 1
    exact GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ
  have key : ∀ x, x = 0 + 1 • mu →
      GlobalTheory.UT.cst (FractionRing V) z (coef s g' w x) * (rigV D (TF (R := V) (FractionRing V)).hom z J).val *
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val =
      GlobalTheory.UT.cst (FractionRing V) z κ₀ *
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val *
        sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s x) (𝟙 _) z J).val *
        (Geo.Tor.val w (𝟙 _) z J).val := by
    rintro x rfl
    have a := GlobalTheory.UT.CoefBasic.isCoef_coef g' hw (0 + 1 • mu) s z J hJ
    rw [pow_one] at a
    obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := FractionRing V) hG 1 mu 0
    have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe mu 0 u hu hc) _ ρ.left z J hJ
    have v := hv u hu hc _ ρ z J hJ
    rw [GlobalTheory.UU.uVal_one D (FractionRing V) _ _ _ hJ, _root_.one_mul, hρ₁] at v
    have m := GlobalTheory.UU.val_famMult_one D (FractionRing V) (𝟙 _) hJ mu 0
    rw [Over.id_left, Category.id_comp] at m
    have m' := congrArg Units.val m
    rw [Units.val_mul] at m'
    have ps : ∀ y, y = mu → (Geo.Tor.val (D.psi y) (jFK (R := V) (FractionRing V)) z J).val =
        (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J).val := by
      rintro _ rfl; rfl
    rw [ps _ (add_zero mu)] at m'
    have b₁ : ρ.left ≫ (DegPre.trF D (FractionRing V) mu).left ≫ GlobalTheory.FieldBaseChange.famBase D (FractionRing V) = 𝟙 _ := by
      rw [GlobalTheory.FieldBaseChange.trF_famBase]
      exact congrArg (fun q => q.left) hρ₁
    have b₂ : (ρ.left ≫ (DegPre.trF D (FractionRing V) mu).left) ≫ (DegPre.prB D (FractionRing V)).left =
        (padd D.P.A (DegPre.cT D _ mu) g'.b).left := by
      rw [← Over.comp_left, ← Over.comp_left, Category.assoc, DegPre.trF, lift_snd,
        GlobalTheory.IntFam.TermLift.comp_padd, hρ₂, ← Category.assoc, toUnit_unique (ρ ≫ toUnit _) (toUnit _)]
      exact congrArg (fun q => Over.Hom.left q)
        (show padd D.P.A g'.b (DegPre.cT D _ mu) = padd D.P.A (DegPre.cT D _ mu) g'.b from mul_comm _ _)
    rw [s0, Category.assoc, b₁, b₂] at e
    rw [a, e, v]
    have c₀ : GlobalTheory.FieldBaseChange.constVal (𝟙 (TF (R := V) (FractionRing V)).left) z κ₀ = GlobalTheory.UT.cst (FractionRing V) z κ₀ := rfl
    rw [c₀]
    simp only [id]
    linear_combination (GlobalTheory.UT.cst (FractionRing V) z κ₀ * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J *
      (Geo.Tor.val (g'.s (0 + 1 • mu)) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val) * m'
  have := key mu (by rw [zero_add, one_smul])
  exact this

end GlobalTheory.Poinc.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarAdditiveComplexLinearOne
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.GlobLin

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_add (α β : A.Fld) (i : A.ι) : A.loc (α + β) i = fun v => A.loc α i v + A.loc β i v := by
  funext v
  unfold HolAtlas.loc
  split_ifs
  exacts [rfl, (add_zero _).symm]

theorem loc_smul (c : ℂ) (α : A.Fld) (i : A.ι) : A.loc (c • α) i = fun v => c • A.loc α i v := by
  funext v
  unfold HolAtlas.loc
  split_ifs
  exacts [rfl, (smul_zero _).symm]

theorem target_mem_nhds (x : A.Pt) : (A.e x.1.1).target ∈ 𝓝 x.crd :=
  (A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2)

theorem differentiableAt_coef {α : A.Fld} (h : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
  ((h.smooth x.1.1 S).contDiffAt (target_mem_nhds A x)).differentiableAt (by simp)

theorem loc_one_eventuallyEq (x : A.Pt) : A.loc 1 x.1.1 =ᶠ[𝓝 x.crd] fun _ => 1 :=
  Filter.eventually_of_mem (target_mem_nhds A x) fun v hv => by
    rw [HolAtlas.loc, dite_eq_left hv]
    rfl

end GlobalTheory.CxForm.GlobLin


open GlobalTheory.CxForm.GlobLin in
theorem GlobalTheory.CxForm.HolAtlas.del_dbar_linear : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n),
    (A.del 1 = 0 ∧ A.dbar 1 = 0) ∧
    ∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β →
      A.del (α + β) = A.del α + A.del β ∧ A.dbar (α + β) = A.dbar α + A.dbar β ∧
      A.del (c • α) = c • A.del α ∧ A.dbar (c • α) = c • A.dbar α := by
  intro M _ n A
  refine ⟨⟨funext fun x => ?_, funext fun x => ?_⟩, fun c α β hα hβ =>
    ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => ?_, funext fun x => ?_⟩⟩
  all_goals obtain ⟨hadd, hsmul, -, hgerm, hconst⟩ := _root_.GlobalTheory.CxForm.delAt_dbarAt_linear_local n x.crd
  · exact (hgerm _ _ (loc_one_eventuallyEq A x)).1.trans (hconst 1).1
  · exact (hgerm _ _ (loc_one_eventuallyEq A x)).2.trans (hconst 1).2
  · rw [HolAtlas.del, loc_add]
    exact (hadd _ _ (differentiableAt_coef A hα x) (differentiableAt_coef A hβ x)).1
  · rw [HolAtlas.dbar, loc_add]
    exact (hadd _ _ (differentiableAt_coef A hα x) (differentiableAt_coef A hβ x)).2
  · rw [HolAtlas.del, loc_smul]
    exact (hsmul _ c (differentiableAt_coef A hα x)).1
  · rw [HolAtlas.dbar, loc_smul]
    exact (hsmul _ c (differentiableAt_coef A hα x)).2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarChainRuleHolomorphicPullback
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CxForm.PullChain

variable {n : ℕ}

theorem repr_algebraMap (t : ℂ) (S : Finset (Fin (n + n))) :
    (bas n).repr (algebraMap ℂ (Alt n) t) S = if S = ∅ then t else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, ← bas_empty, map_smul, Module.Basis.repr_self]
  by_cases h : S = ∅ <;> simp [Finsupp.single_apply, h, eq_comm]

theorem delAt_dbarAt_algebraMap (g : V n → ℂ) (v : V n) :
    delAt (fun x => algebraMap ℂ (Alt n) (g x)) v = ∑ a, del g v (coordVec a) • dz a ∧
    dbarAt (fun x => algebraMap ℂ (Alt n) (g x)) v = ∑ a, dbar g v (coordVec a) • dzb a := by
  have h : (fun x => algebraMap ℂ (Alt n) (g x)) = fun x => g x • bas n ∅ := by
    funext x; rw [Algebra.algebraMap_eq_smul_one, bas_empty]
  rw [h]
  constructor
  · unfold delAt
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_smul (T := fun f => del f v (coordVec a)) (by simp) g, bas_empty, mul_smul_comm, mul_one]
  · unfold dbarAt
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_smul (T := fun f => dbar f v (coordVec a)) (by simp) g, bas_empty, mul_smul_comm, mul_one]

theorem differentiableAt_repr_algebraMap {g : V n → ℂ} {v : V n} (hg : DifferentiableAt ℝ g v)
    (S : Finset (Fin (n + n))) : DifferentiableAt ℝ (fun x => (bas n).repr (algebraMap ℂ (Alt n) (g x)) S) v := by
  simp only [repr_algebraMap]
  split_ifs
  exacts [hg, differentiableAt_const _]

theorem delAt_dbarAt_pull_comp (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (β : V n → Alt n) (v : V m)
    (hU : IsOpen U) (hv : v ∈ U) (hτ : DifferentiableOn ℂ τ U)
    (hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (β y) S) (τ v)) :
    delAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (delAt β (τ v)) ∧
    dbarAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (dbarAt β (τ v)) := by
  have hτv : DifferentiableAt ℂ τ v := hτ.differentiableAt (hU.mem_nhds hv)
  have hg : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (β (τ x)) S) v :=
    fun S => (hβ S).comp v (hτv.restrictScalars ℝ)
  have hPd : ∀ S T, DifferentiableAt ℝ (fun x => (bas m).repr (pull (fderiv ℂ τ x) (bas n S)) T) v :=
    fun S T => ((_root_.GlobalTheory.PullSmooth.contDiffOn_repr_pull_fderiv m n τ U (bas n S) hU hτ T).contDiffAt (hU.mem_nhds hv)).differentiableAt (by simp)
  have hA : ∀ S T, DifferentiableAt ℝ
      (fun x => (bas m).repr (algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S)) T) v :=
    fun S T => differentiableAt_repr_algebraMap (hg S) T
  have hprod : ∀ S T, DifferentiableAt ℝ (fun x => (bas m).repr
      (algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S)) T) v :=
    fun S => (_root_.GlobalTheory.CxForm.contDiff_coeff_mul m m (fun x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S))
      (fun x => pull (fderiv ℂ τ x) (bas n S))).2 v (hA S) (hPd S)
  have hexp : (fun x => pull (fderiv ℂ τ x) (β (τ x))) = fun x => ∑ S,
      algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S) := by
    funext x
    conv_lhs => rw [← (bas n).sum_repr (β (τ x))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Algebra.smul_def, map_mul, AlgHom.commutes]
  have hsum := (_root_.GlobalTheory.CxForm.delAt_dbarAt_linear_local m v).2.2.1 (Finset (Fin (n + n))) Finset.univ
    (fun S x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S))
    (fun S _ => hprod S)
  have hL := fun S => _root_.GlobalTheory.CxForm.FormMul.leibniz_of_comm m (fun x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S))
    (fun x => pull (fderiv ℂ τ x) (bas n S)) v (algebraMap ℂ (Alt m) ((bas n).repr (β (τ v)) S)) (hA S) (hPd S)
  have hcl := fun S => _root_.GlobalTheory.CxForm.PullDelClosed.delAt_dbarAt_pull_fderiv m n τ U (bas n S) hU hτ v hv
  have hch := fun S => _root_.GlobalTheory.LineForm.del_dbar_comp_holo_pull m n τ (fun y => (bas n).repr (β y) S) v hτv (hβ S)
  have hfun := fun S => delAt_dbarAt_algebraMap (fun x => (bas n).repr (β (τ x)) S) v
  rw [hexp]
  constructor
  · rw [hsum.1]
    have key : ∀ S, delAt (fun x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S)) v =
        pull (fderiv ℂ τ v) ((∑ a, del (fun y => (bas n).repr (β y) S) (τ v) (coordVec a) • dz a) * bas n S) := by
      intro S
      rw [(hL S).1 (fun a => (Algebra.commutes _ _).symm), (hcl S).1, mul_zero, add_zero, (hfun S).1, (hch S).1,
        map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [key, ← map_sum]
    congr 1
    unfold delAt coefwise
    simp only [Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_comm
  · rw [hsum.2]
    have key : ∀ S, dbarAt (fun x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S)) v =
        pull (fderiv ℂ τ v) ((∑ a, dbar (fun y => (bas n).repr (β y) S) (τ v) (coordVec a) • dzb a) * bas n S) := by
      intro S
      rw [(hL S).2 (fun a => (Algebra.commutes _ _).symm), (hcl S).2, mul_zero, add_zero, (hfun S).2, (hch S).2,
        map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [key, ← map_sum]
    congr 1
    unfold dbarAt coefwise
    simp only [Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_comm

end GlobalTheory.CxForm.PullChain
end
end

