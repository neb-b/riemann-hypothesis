module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniformisationOfComplexConjugateKeyDatum
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.ConjUnif

open GlobalTheory.ArchMetricCompare

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g : ℕ}

theorem le_pull_id (x : Sp ℂ ⟶ A.left) (j : (L.pull (𝟙 A.left)).ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull (𝟙 A.left)).U j ↔ ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit) := by
  rw [le_pull_iff, Category.comp_id]

def pullId (u : HolUnif A L g) : HolUnif A (L.pull (𝟙 A.left)) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr j := u.fr (j PUnit.unit)
  fr_hol j := by
    have e : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull (𝟙 A.left)).U j} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)} :=
      Set.ext fun z => le_pull_id _ j
    rw [e]
    exact u.fr_hol _
  fr_ne j z hz := u.fr_ne _ z ((le_pull_id _ j).1 hz)
  fr_compat j j' z hz := by
    obtain ⟨hj, hj'⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [val_pull_g L _ _ j j' hz, u.fr_compat _ _ z
      ((top_le_preimage_inf _ _ _).2 ⟨(le_pull_id _ j).1 hj, (le_pull_id _ j').1 hj'⟩)]
    congr 2

variable {ψ : A'.left ⟶ A.left} (h : IsGrpPullback A' A cj ψ)

theorem cj_le (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (j : (L.pull ψ).ι) :
    ⊤ ≤ (cjPt h x).left ⁻¹ᵁ (L.pull ψ).U j ↔ ⊤ ≤ x.left ⁻¹ᵁ L.U (j PUnit.unit) := by
  refine (le_pull_iff L _ _ j).trans ?_
  rw [cjPt_comp]
  exact le_cj_iff _ _

def conjPull (u : HolUnif A L g) : HolUnif A' (L.pull ψ) g where
  ex := (cjUnif h (pullId u)).ex
  ex_add := (cjUnif h (pullId u)).ex_add
  ex_onto := (cjUnif h (pullId u)).ex_onto
  Λ := (cjUnif h (pullId u)).Λ
  ker := (cjUnif h (pullId u)).ker
  discrete := (cjUnif h (pullId u)).discrete
  full := (cjUnif h (pullId u)).full
  hol := (cjUnif h (pullId u)).hol
  fr j z := star (u.fr (j PUnit.unit) (star z))
  fr_hol j := by
    have e : {z | ⊤ ≤ ((cjUnif h (pullId u)).ex z).left ⁻¹ᵁ (L.pull ψ).U j} =
        {z | star z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)}} :=
      Set.ext fun z => cj_le h _ j
    rw [e]
    exact differentiableOn_star (u.hol _ 0).1 (u.fr_hol _)
  fr_ne j z hz := star_ne_zero.2 (u.fr_ne _ _ ((cj_le h _ j).1 hz))
  fr_compat j j' z hz := by
    obtain ⟨hj, hj'⟩ := (top_le_preimage_inf _ _ _).1 hz
    have hm := (top_le_preimage_inf _ _ _).2 ⟨(cj_le h _ j).1 hj, (cj_le h _ j').1 hj'⟩
    rw [val_pull_g L _ _ j j' hz, u.fr_compat _ _ _ hm, star_mul']
    congr 1
    exact ((congrArg (fun x => valAt' x _ _) (cjPt_comp h (u.ex (star z)))).trans (val_cj _ _ _)).symm

theorem conjPull_isAH (u : HolUnif A L g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hA : u.IsAH Hm χ) :
    (conjPull h u).IsAH (Hm.map star) fun l => star (χ ⟨star l.1, l.2⟩) := by
  have h0 : (pullId u).IsAH Hm χ :=
    ⟨hA.1, hA.2.1, hA.2.2.1, fun l j z hj => hA.2.2.2 l _ z ((le_pull_id _ j).1 hj)⟩
  have h1 := cj_isAH h _ h0
  exact ⟨h1.1, h1.2.1, h1.2.2.1, fun l j z hj =>
    h1.2.2.2 l j z ((cj_le_pull h _ j).2 ((le_pull_id _ j).2 ((cj_le h _ j).1 hj)))⟩

theorem exists_inv {X : Scheme.{0}} {M N : LB X} (w : LB.Iso M N) (hw : w.IsGen) :
    ∃ w' : LB.Iso N M, w'.IsGen ∧ ∀ (x : Sp ℂ ⟶ X) (j : N.ι) (i : M.ι), ⊤ ≤ x ⁻¹ᵁ (N.U j ⊓ M.U i) →
      valAt' x (M.U i ⊓ N.U j) (w'.s (i, j)).val = (valAt' x (N.U j ⊓ M.U i) (w.s (j, i)).val)⁻¹ := by
  have le : ∀ p : M.ι × N.ι, M.U p.1 ⊓ N.U p.2 ≤ N.U p.2 ⊓ M.U p.1 := fun p y hy => ⟨hy.2, hy.1⟩
  refine ⟨⟨fun p => (res (le p) (w.s (p.2, p.1)))⁻¹⟩, fun p q => unit_ext fun y hy => ?_, fun x j i hx => ?_⟩
  · have hm : (𝟙 X : X ⟶ X) y ∈ N.U p.2 ⊓ M.U p.1 ⊓ (N.U q.2 ⊓ M.U q.1) := ⟨le p hy.1, le q hy.2⟩
    have e := congrArg (gm (𝟙 X) y (N.U p.2 ⊓ M.U p.1 ⊓ (N.U q.2 ⊓ M.U q.1))) (hw (p.2, p.1) (q.2, q.1))
    have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div M N (𝟙 X) y (p.2, p.1) (q.2, q.1) hm) (gm_res _ y _ hm _))))
    have v : ∀ p : M.ι × N.ι, y ∈ M.U p.1 ⊓ N.U p.2 →
        gm (𝟙 X) y (M.U p.1 ⊓ N.U p.2) (res (le p) (w.s (p.2, p.1)))⁻¹ =
        (gm (𝟙 X) y (N.U p.2 ⊓ M.U p.1) (w.s (p.2, p.1)))⁻¹ := fun p hp =>
      (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))
    refine ((gm_res _ y _ hy _).trans ((v p hy.1).trans (congrArg (·⁻¹) e'))).trans (Eq.symm ?_)
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div N M (𝟙 X) y p q hy)
      ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
    rw [mul_inv, mul_inv, inv_inv, mul_comm (gm (𝟙 X) y _ (M.g p.1 q.1))]
    rfl
  · have hx' : ⊤ ≤ x ⁻¹ᵁ (M.U i ⊓ N.U j) := by rwa [inf_comm]
    exact (valAt'_units_inv x hx' _).trans (congrArg _ (valAt'_res x (le (i, j)) _ hx'))

theorem exists_conj_unif : ∀ (x x' : KeyIn ℂ), KeyPB x' x (starRingEnd ℂ) → ∀ (hg : x'.P.g = x.P.g) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → ∃ (u' : HolUnif x'.P.A x'.P.L g) (χ' : u'.Λ → ℂ) (θ' : (Fin g → ℂ) → ℂ) (Fd' : Set (Fin g → ℂ)), u'.IsAH (Hm.map (starRingEnd ℂ)) χ' ∧ u'.IsRig x'.rig ∧ u'.IsFn x'.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume ∧ (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm (Hm.map (starRingEnd ℂ)) z z).re)) / (volume Fd').toReal = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧ ∀ (cf : Fin x.P.g → ℂ) (w : epsR ℂ ⟶ x.P.A) (w' : epsR ℂ ⟶ x'.P.A) (W : Fin g → ℂ), IsLieComb cf x.v w → IsLieComb (fun i => (starRingEnd ℂ) (cf (i.cast hg))) x'.v w' → u.IsDiff W w → u'.IsDiff (fun i => (starRingEnd ℂ) (W i)) w' := by
  rintro x x' ⟨φ, he, w, hg', F, hφ, hw, hrig, hth, hF, hε, hv⟩ hg g u Hm χ θ Fd ⟨hA, hR, hθ, hFd⟩
  rw [KeyFibre.eq_dualMapR_of_algebraMap _ F hF hε] at hv
  obtain ⟨w', hw', hinv⟩ := exists_inv w hw
  have hP : (x.P.L.pull φ).IsLB := DVR.linComb_isLB x.P.L x.P.isLB _ _
  let u₁ := conjPull hφ u
  have me : MeasurableEmbedding (star : (Fin g → ℂ) → Fin g → ℂ) :=
    (starL' ℝ (A := Fin g → ℂ)).toHomeomorph.measurableEmbedding
  have fr : ∀ (j : x.P.L.ι) (i : x'.P.L.ι) (z : Fin g → ℂ),
      ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ ((x.P.L.pull φ).U (fun _ => j) ⊓ x'.P.L.U i) →
      valAt' (u₁.ex z).left ((x.P.L.pull φ).U (fun _ => j) ⊓ x'.P.L.U i) (w.s (fun _ => j, i)).val *
        (carry u₁ hP x'.P.isLB hw').fr i z = star (u.fr j (star z)) := by
    intro j i z hz
    obtain ⟨hj, hi⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [carry_fr u₁ hP x'.P.isLB hw' i (fun _ => j) z hi hj, hinv _ _ _ hz]
    exact mul_inv_cancel_left₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j, i))) _
  refine ⟨carry u₁ hP x'.P.isLB hw', _, fun z => star (θ (star z)), star ⁻¹' Fd,
    carry_isAH hP x'.P.isLB hw' (conjPull_isAH hφ u hA), ?_, ?_, cj_domain hφ (pullId u) hFd, ?_, ?_⟩
  · intro i hi
    have h0 : (u₁.ex 0).left = eSec x'.P.A := by
      rw [(u₁.ker 0).2 u₁.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    have h0' : (u.ex 0).left = eSec x.P.A := by
      rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    obtain ⟨j, hj⟩ := exists_chart_at hP (u₁.ex 0).left
    have hi' : ⊤ ≤ (u₁.ex 0).left ⁻¹ᵁ x'.P.L.U (i PUnit.unit) := by
      rw [h0]
      exact fun p hp => mem_pull.1 (hi hp)
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hi'⟩
    have e := fr (j PUnit.unit) (i PUnit.unit) 0 hz
    have hj' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ x.P.L.U (j PUnit.unit) := by
      have := (cj_le hφ _ j).1 hj
      rwa [star_zero] at this
    rw [h0'] at hj'
    have hj'' : ⊤ ≤ (x.P.L.pull (eSec x.P.A)).U fun _ => j PUnit.unit := fun p hp => mem_pull.2 (hj' hp)
    rw [star_zero, hR _ hj'', ← val_cj, Category.comp_id, h0] at e
    rw [h0] at hz
    exact mul_left_cancel₀ (valAt'_unit_ne_zero _ hz _)
      (e.trans (val_rig he w x'.rig x.rig hrig (j PUnit.unit) (i PUnit.unit) hz))
  · intro i z hi
    obtain ⟨j, hj⟩ := exists_chart_at hP (u₁.ex z).left
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hi⟩
    have e := fr (j PUnit.unit) i z hz
    have e₁ := val_via w x.th x'.th hth (u₁.ex z).left (j PUnit.unit) i hz
    have e₂ : valAt' ((u₁.ex z).left ≫ φ) (x.P.L.U (j PUnit.unit)) (x.th.f (j PUnit.unit)) =
        star (θ (star z)) * star (u.fr (j PUnit.unit) (star z)) :=
      (congrArg (fun x => valAt' x _ _) (cjPt_comp hφ (u.ex (star z)))).trans ((val_cj _ _ _).trans
        ((congrArg star (hθ _ (star z) ((cj_le hφ _ j).1 hj))).trans (star_mul' _ _)))
    refine mul_left_cancel₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j PUnit.unit, i))) ?_
    refine e₁.symm.trans (e₂.trans ?_)
    rw [← e]
    exact mul_left_comm _ _ _
  · rw [measurePreserving_star.measure_preimage_emb me Fd, ← measurePreserving_star.setIntegral_preimage_emb me _ Fd]
    refine congrArg (fun t : (Fin g → ℂ) → ℝ => (∫ z in star ⁻¹' Fd, t z) / (volume Fd).toReal) (funext fun z => ?_)
    rw [norm_star]
    exact congrArg (fun t : ℝ => ‖θ (star z)‖ ^ 2 * Real.exp (-Real.pi * t)) (hermSq_star Hm z)
  · intro cf v v' W h₁ h₂ hd
    have h₃ : ∀ (n : ℕ) (e : n = x.P.g), IsLieComb (fun i => cf (i.cast e)) (fun i : Fin n => x.v (i.cast e)) v := by
      rintro _ rfl
      exact h₁
    have e := (lieComb_baseChange ℂ ℂ _ _ _ φ hφ _ _ v _ x'.v v' hv (h₃ _ hg)).2 h₂
    exact cj_isDiff hφ (pullId u) (GlobalTheory.Reg.isTangent_of_isLieComb x.basis.1 h₁) e hd

end GlobalTheory.ConjUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem etale_pullback_torsion {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {n : ℕ} (hn : IsUnit (n : Γ(S', ⊤))) :
    Etale ((Over.pullback f).obj (torsion G n)).hom := by
  have hs : Smooth ((Over.pullback f).obj G).hom := inferInstanceAs (Smooth (pullback.snd G.hom f))
  have he : Etale ((Over.pullback f).map (mulN G n)).left := by
    rw [GrpTangent.pullback_map_mulN]
    exact GrpTangent.etale_mulN _ hn
  have h := ((IsPullback.of_hasPullback (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).map (Over.pullback f)).map
    (Over.forget S')
  have h1 : Etale ((Over.pullback f).map (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G))).left :=
    MorphismProperty.of_isPullback (P := @Etale) h he
  have h2 : Etale ((Over.pullback f).obj (𝟙_ (Over S))).hom :=
    inferInstanceAs (Etale (pullback.snd (𝟙 S) f))
  have e := Over.w ((Over.pullback f).map (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)))
  have h3 : Etale (((Over.pullback f).map (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G))).left ≫
    ((Over.pullback f).obj (𝟙_ (Over S))).hom) := inferInstance
  rw [e] at h3
  exact h3

theorem etale_pullback_tensor {S S' : Scheme.{0}} (f : S' ⟶ S) (A B : Over S)
    (hA : Etale ((Over.pullback f).obj A).hom) (hB : Etale ((Over.pullback f).obj B).hom) :
    Etale ((Over.pullback f).obj (A ⊗ B)).hom := by
  have h : Etale ((Over.pullback f).obj A ⊗ (Over.pullback f).obj B).hom :=
    inferInstanceAs (Etale (pullback.fst ((Over.pullback f).obj A).hom ((Over.pullback f).obj B).hom ≫
      ((Over.pullback f).obj A).hom))
  rw [← Over.w (Functor.Monoidal.μIso (Over.pullback f) A B).inv]
  have : IsIso (Functor.Monoidal.μIso (Over.pullback f) A B).inv.left :=
    inferInstanceAs (IsIso ((Over.forget S').map (Functor.Monoidal.μIso (Over.pullback f) A B).inv))
  infer_instance

theorem torsion_universal {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) :
    torsion.ι G n ^ n = 1 ∧ ∀ (T : Over S) (x : T ⟶ G), x ^ n = 1 → ∃ t : T ⟶ torsion G n, t ≫ torsion.ι G n = x := by
  refine ⟨?_, fun T x hx => ⟨pullback.lift x (toUnit T) ?_, pullback.lift_fst _ _ _⟩⟩
  · rw [← GrpTangent.comp_mulN]
    refine pullback.condition.trans ?_
    rw [Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  · rw [GrpTangent.comp_mulN, hx, Hom.one_def]

theorem exists_universal_torsion_pair :
    Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] (X Y : Out.PolAV (Sp R)) (k : ℕ), 0 < k → ∃ (T₀ : Over (Sp R)) (x₀ : T₀ ⟶ X.A) (y₀ : T₀ ⟶ Y.A), x₀ ^ k = 1 ∧ y₀ ^ k = 1 ∧ (∀ (T : Over (Sp R)) (x : T ⟶ X.A) (y : T ⟶ Y.A), x ^ k = 1 → y ^ k = 1 → ∃ t : T ⟶ T₀, x = t ≫ x₀ ∧ y = t ≫ y₀) ∧ ∀ a b : Γ(T₀.left, ⊤), (∀ (k' : Type) [Field k'] [IsAlgClosed k'] [CharZero k'] (β : R →+* k') (t : Over.mk (spMap β) ⟶ T₀), t.left.appTop.hom a = t.left.appTop.hom b) → a = b := by
  intro hL R _ _ _ X Y k hk
  have fin : ∀ P : Out.PolAV (Sp R), IsFinite (torsion P.A k).hom ∧ Flat (torsion P.A k).hom := fun P => by
    obtain ⟨h1, h2, -⟩ := hL.mulN (Sp R) P k hk
    rw [Out.mulA, ← GrpTangent.mulN_eq_pow] at h1 h2
    exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) (GrpTangent.isPullback_torsion P.A k) h1,
      MorphismProperty.of_isPullback (P := @Flat) (GrpTangent.isPullback_torsion P.A k) h2⟩
  haveI : CharZero (FractionRing R) := algebraRat.charZero _
  have hu : IsUnit (k : Γ(Sp (FractionRing R), ⊤)) := by
    have : IsUnit (k : FractionRing R) := (Nat.cast_ne_zero.mpr hk.ne').isUnit
    simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
  have et : ∀ P : Out.PolAV (Sp R),
      Etale ((Over.pullback (spMap (algebraMap R (FractionRing R)))).obj (torsion P.A k)).hom := fun P => by
    have := P.isAb.comm
    have := P.isAb.smooth
    exact etale_pullback_torsion _ P.A hu
  obtain ⟨hX, uX⟩ := torsion_universal X.A k
  obtain ⟨hY, uY⟩ := torsion_universal Y.A k
  refine ⟨torsion X.A k ⊗ torsion Y.A k, fst _ _ ≫ torsion.ι X.A k, snd _ _ ≫ torsion.ι Y.A k, ?_, ?_, ?_, ?_⟩
  · rw [← comp_pow, hX, comp_one]
  · rw [← comp_pow, hY, comp_one]
  · intro T x y hx hy
    obtain ⟨s, hs⟩ := uX T x hx
    obtain ⟨t, ht⟩ := uY T y hy
    exact ⟨lift s t, by rw [lift_fst_assoc, hs], by rw [lift_snd_assoc, ht]⟩
  · obtain ⟨f1, f2⟩ := fin X
    obtain ⟨g1, g2⟩ := fin Y
    refine GlobalTheory.LamF.eq_of_geomPoints R (FractionRing R) _ ?_ ?_ (etale_pullback_tensor _ _ _ (et X) (et Y))
    · exact inferInstanceAs (IsFinite (pullback.fst (torsion X.A k).hom (torsion Y.A k).hom ≫ (torsion X.A k).hom))
    · exact inferInstanceAs (Flat (pullback.fst (torsion X.A k).hom (torsion Y.A k).hom ≫ (torsion X.A k).hom))

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyIdentitiesDescendFieldToDedekind
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FamDescent

theorem lamEq_descend {R k : Type} [CommRing R] [IsDedekindDomain R] [Field k] (f : R →+* k)
    (hf : Function.Injective f) {X Y A B : Over (Sp R)} {X' Y' A' B' : Over (Sp k)} [GrpObj X] [GrpObj Y]
    [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj A'] [IsCommMonObj A'] [GrpObj B'] [IsCommMonObj B']
    (hX : IsAbelianScheme X) (hY : IsAbelianScheme Y)
    {x : X'.left ⟶ X.left} {y : Y'.left ⟶ Y.left} {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left}
    (hx : IsPullback x X'.hom X.hom (spMap f)) (hy : IsPullback y Y'.hom Y.hom (spMap f))
    (hA : IsGrpPullback A' A (spMap f) a) (hB : IsGrpPullback B' B (spMap f) b)
    {L : LB A.left} {M : LB B.left} {L' : LB A'.left} {M' : LB B'.left}
    (hL : L.IsLB) (hM : M.IsLB) (hL' : L'.IsLB) (hM' : M'.IsLB) (iL : LBIso (L.pull a) L') (iM : LBIso (M.pull b) M')
    {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B} [IsMonHom f₁] [IsMonHom f₂] [IsMonHom g₁] [IsMonHom g₂]
    {f₁' : X' ⟶ A'} {f₂' : Y' ⟶ A'} {g₁' : X' ⟶ B'} {g₂' : Y' ⟶ B'}
    (e₁ : f₁'.left ≫ a = x ≫ f₁.left) (e₂ : f₂'.left ≫ a = y ≫ f₂.left)
    (e₃ : g₁'.left ≫ b = x ≫ g₁.left) (e₄ : g₂'.left ≫ b = y ≫ g₂.left)
    (H : LamEq L' f₁' f₂' M' g₁' g₂') : LamEq L f₁ f₂ M g₁ g₂ := by
  obtain ⟨Pic, _, cl, pl, hiso, -, -, hcomp, hlin, -⟩ := CechPicMul.exists_picardGroup
  have hpull : ∀ {U V : Scheme.{0}} (N : LB U), N.IsLB → ∀ g : V ⟶ U, (N.pull g).IsLB ∧ cl (N.pull g) = pl g (cl N) :=
    fun N hN g => ⟨(hlin _ _ N hN _ _ _).1, (hlin _ _ N hN _ _ _).2.trans (by simp)⟩
  let π := pullback.fst (X ⊗ Y).hom (spMap f)
  let p := pullback.snd (X ⊗ Y).hom (spMap f)
  have hπ : π ≫ (X ⊗ Y).hom = p ≫ spMap f := pullback.condition
  let u : Over.mk p ⟶ X' := Over.homMk (hx.lift (π ≫ (fst X Y).left) p (by rw [Category.assoc, Over.w, hπ]))
    (hx.lift_snd _ _ _)
  let v : Over.mk p ⟶ Y' := Over.homMk (hy.lift (π ≫ (snd X Y).left) p (by rw [Category.assoc, Over.w, hπ]))
    (hy.lift_snd _ _ _)
  have hu : u.left ≫ x = π ≫ (fst X Y).left := hx.lift_fst _ _ _
  have hv : v.left ≫ y = π ≫ (snd X Y).left := hy.lift_fst _ _ _
  let U : Over.mk ((Over.mk p).hom ≫ spMap f) ⟶ X ⊗ Y := Over.homMk π hπ
  have gen : ∀ {C : Over (Sp R)} {C' : Over (Sp k)} [GrpObj C] [GrpObj C'] {c : C'.left ⟶ C.left}
      (hC : IsGrpPullback C' C (spMap f) c) {N : LB C.left} {N' : LB C'.left}, N.IsLB → N'.IsLB →
      LBIso (N.pull c) N' → ∀ (s : X ⟶ C) (t : Y ⟶ C) (s' : X' ⟶ C') (t' : Y' ⟶ C'),
      s'.left ≫ c = x ≫ s.left → t'.left ≫ c = y ≫ t.left →
      cl ((cubeLB C ![fst X Y ≫ s, snd X Y ≫ t] N).pull π) = cl (cubeLB C' ![u ≫ s', v ≫ t'] N') := by
    intro C C' _ _ c hC N N' hN hN' iN s t s' t' hs ht
    have e : pl c (cl N) = cl N' := (hpull N hN c).2.symm.trans ((hiso _ _ _ (hpull N hN c).1 hN').2 iN)
    refine (hpull _ (LamCalc.cubeLB_isLB hN _) π).2.trans ?_
    refine (congrArg (pl π) (hlin _ _ N hN _ _ _).2).trans (Eq.trans ?_ (hlin _ _ N' hN' _ _ _).2.symm)
    rw [map_prod]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [map_zpow, ← hcomp, ← e, ← hcomp]
    refine congrArg (fun z => pl z (cl N) ^ _) (Eq.symm ?_)
    refine lamBC_psum_push hC _ _ U (fun i => ?_) I.down
    fin_cases i
    · refine Over.OverMorphism.ext ?_
      show (u.left ≫ s'.left) ≫ c = π ≫ (fst X Y).left ≫ s.left
      rw [Category.assoc, hs, ← Category.assoc, hu, Category.assoc]
    · refine Over.OverMorphism.ext ?_
      show (v.left ≫ t'.left) ≫ c = π ≫ (snd X Y).left ≫ t.left
      rw [Category.assoc, ht, ← Category.assoc, hv, Category.assoc]
  have zero : ∀ {C : Over (Sp R)} [GrpObj C] [IsCommMonObj C] {N : LB C.left}, N.IsLB →
      ∀ (s : X ⟶ C) (t : Y ⟶ C), IsMonHom s → IsMonHom t →
      cl ((cubeLB C ![fst X Y ≫ s, snd X Y ≫ t] N).pull (eSec (X ⊗ Y))) = 1 := by
    intro C _ _ N hN s t _ _
    refine (hpull _ (LamCalc.cubeLB_isLB hN _) _).2.trans ?_
    rw [LamCalc.class_cubeLB cl (fun z => pl z (cl N)) (fun I _ φ ε => (hlin _ _ N hN I φ ε).2)]
    have w : ∀ z : X ⊗ Y ⟶ C, η[X ⊗ Y] ≫ z = 1 →
        pl (eSec (X ⊗ Y)) (pl z.left (cl N)) = pl (1 : 𝟙_ (Over (Sp R)) ⟶ C).left (cl N) := fun z hz => by
      rw [← hcomp, ← hz]; rfl
    have o : (1 : 𝟙_ (Over (Sp R)) ⟶ C) = η[C] := by simp [Hom.one_def]
    have h₁ : η[X ⊗ Y] ≫ fst X Y ≫ s = 1 := by rw [o]; exact IsMonHom.one_hom _
    have h₂ : η[X ⊗ Y] ≫ snd X Y ≫ t = 1 := by rw [o]; exact IsMonHom.one_hom _
    simp only [map_mul, map_inv]
    rw [w _ h₁, w _ h₂, w 1 (MonObj.comp_one _), w _ (by rw [MonObj.comp_mul, h₁, h₂, _root_.mul_one])]
    simp
  have cL := LamCalc.cubeLB_isLB hL ![fst X Y ≫ f₁, snd X Y ≫ f₂]
  have cM := LamCalc.cubeLB_isLB hM ![fst X Y ≫ g₁, snd X Y ≫ g₂]
  refine _root_.GlobalTheory.IsoDescent.lbIso_of_field R k f hf (X ⊗ Y) (AbelianSchemeGerms.isAbelianScheme_tensor X Y hX hY) _ π p (IsPullback.of_hasPullback _ _)
    _ _ cL cM ?_ ?_
  · exact (hiso _ _ _ (hpull _ cL _).1 (hpull _ cM _).1).1
      ((zero hL f₁ f₂ ‹_› ‹_›).trans (zero hM g₁ g₂ ‹_› ‹_›).symm)
  · refine (hiso _ _ _ (hpull _ cL _).1 (hpull _ cM _).1).1
      ((gen hA hL hL' iL _ _ _ _ e₁ e₂).trans (Eq.trans ?_ (gen hB hM hM' iM _ _ _ _ e₃ e₄).symm))
    exact (hiso _ _ _ (LamCalc.cubeLB_isLB hL' _) (LamCalc.cubeLB_isLB hM' _)).2 (LamCalc.lbIso_of_lamEq H u v)

theorem isFam_descend : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDedekindDomain R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (k : Type) [Field k] (ω' : k) (C' : Ell H k ω') (f : R →+* k) (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp k)) (m : SABMap T'.t T.t (spMap f)) (ψ' : L → (C'.P.A ⟶ T'.t.G)), Function.Injective f → EllMap C' C f φ → (∀ a, (ψ' a).left ≫ m.φ = φ ≫ (ψ a).left) → IsFam C' T' h L ψ' → IsFam C T h L ψ := by
  intro _ E _ _ _ H R _ _ ω C D h T L ψ k _ ω' C' f φ T' m ψ' hf hE hψ hF
  obtain ⟨-, ⟨-, hC, iC⟩, -, hact⟩ := hE
  obtain ⟨hlin, hadd, hsm, hlam⟩ := hF
  have : IsSchemeTheoreticallyDominant (spMap f) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom f) hf
  have : QuasiCompact (spMap f) := inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom f)))
  have := C.P.isAb.smooth
  have : Flat C.P.A.hom := inferInstance
  have : IsSeparated T.t.G.hom := T.t.semi.separated
  have hm : ∀ a, IsMonHom (ψ a) := fun a =>
    have := (hlin a).isMonHom
    ExtUnique.isMonHom_of_isGrpPullback hC m.cart (ψ' a) (ψ a) (hψ a)
  refine ⟨fun a => ⟨hm a, fun c => ?_⟩, fun a b => ?_, fun s a => ?_, fun a b => ?_⟩
  · refine ExtUnique.over_hom_ext_of_isPullback (j := spMap f) hC.1 ?_
    have e := congrArg (fun z => z.left ≫ m.φ) ((hlin a).comm c)
    simp only [Over.comp_left, Category.assoc, Serre.comapAct_act] at e ⊢
    rw [hψ, m.act, ← Category.assoc, ← Category.assoc, hact, hψ, Category.assoc, Category.assoc] at e
    exact e
  · refine ExtUnique.over_hom_ext_of_isPullback (j := spMap f) hC.1 ?_
    let φ₀ : Over.mk (C'.P.A.hom ≫ spMap f) ⟶ C.P.A := Over.homMk φ hC.1.w
    have e := m.cart.2 C'.P.A (ψ' a) (ψ' b) (φ₀ ≫ ψ a) (φ₀ ≫ ψ b) (hψ a).symm (hψ b).symm
    rw [← MonObj.comp_mul] at e
    rw [← hψ, hadd, ← e]
    rfl
  · refine ExtUnique.over_hom_ext_of_isPullback (j := spMap f) hC.1 ?_
    rw [← hψ, hsm, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hψ, Category.assoc]
  · have := hm a
    have := hm b
    have := C.act.hom (h a b)
    exact lamEq_descend f hf C.P.isAb C.P.isAb hC.1 hC.1 m.cart hC T.t.PP.isLB C.P.isLB T'.t.PP.isLB C'.P.isLB
      (LBIso.symm (show LBIso T'.t.PP.L (T.t.PP.L.pull m.φ) from m.lin.imp fun _ h => h.1))
      iC (hψ a) (hψ b) (hact _) (by simp) (hlam a b)

end GlobalTheory.FamDescent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasPeriodOfEllMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem hasPeriod_of_ellMap : Out.PolBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (M K : Type) [Field M] [NumberField M] [Field K] [NumberField K] (j : M →+* K) (ω : 𝓞 M) (ω' : 𝓞 K) (C : Ell H (𝓞 M) ω) (C' : Ell H (𝓞 K) ω') (φ : C'.P.A.left ⟶ C.P.A.left) (x : ℝ), EllMap C' C (RingOfIntegers.mapRingHom j) φ → C.HasPeriod x → C'.HasPeriod x := by
  intro hbc E _ _ _ H M K _ _ _ _ j ω ω' C C' φ x hm hx
  obtain ⟨n, hn, hmean⟩ := hx
  refine ⟨fun s => n (s.comp j), fun s => ⟨(hn _).1, fun r => ?_⟩, ?_⟩
  · rw [(_root_.GlobalTheory.CM.EllComp.ellMap_comp E H _ ω C _ ω' C' _ φ hm).2.2 _ r hbc]
    have e : (s.comp (algebraMap (𝓞 K) K)).comp (RingOfIntegers.mapRingHom j)
        = (s.comp j).comp (algebraMap (𝓞 M) M) := by
      ext a; rfl
    rw [e]
    exact (hn _).2 r
  · rw [GlobalTheory.meanLog_comp]; exact hmean

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsEigenvectorAtOfModel
section
set_option autoImplicit false

namespace GlobalTheory.LamT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

theorem isEigAt_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (x : Sp K ⟶ Xo.X) (t₀ : SAB H (Sp K)) (B : SAB H (Sp (𝓞 K))) (m : SABMap t₀ Xo.univ.t x) (m' : SABMap t₀ B (spMap (algebraMap (𝓞 K) K))) (τ : E →+* ℂ) (w : epsR K ⟶ t₀.G), (∀ a : 𝓞 E, ∃ w' : epsR K ⟶ t₀.G, IsLieComb ![LamF.labK c K τ (a : E)] ![w] w' ∧ w.left ≫ m'.φ ≫ (B.act.act a).left = w'.left ≫ m'.φ) → IsEigAt c τ (w.left ≫ m.φ) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ x t₀ B m m' τ w h a
  obtain ⟨w', ⟨u, hu, hw'⟩, e⟩ := h a
  have h1 : w'.left = spMap (epsScaleR (LamF.labK c K τ (a : E))) ≫ w.left := by
    rw [hw']
    simpa using hu 0
  have h2 : w.left ≫ (t₀.act.act a).left = w'.left := by
    apply m'.cart.1.hom_ext
    · rw [Category.assoc, m'.act a]
      exact e
    · rw [Category.assoc, Over.w (t₀.act.act a), Over.w w, Over.w w']
  rw [Category.assoc, ← m.act a, ← Category.assoc, h2, h1, Category.assoc]
  rfl

end GlobalTheory.LamT
end

