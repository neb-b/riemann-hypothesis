module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0005
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRepUpqMatrixFunction
section
section

noncomputable section

namespace GlobalTheory.PsCo.PcEF.MatrixRepresentation

variable {n : ℕ} (ε : Fin n → Bool) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

abbrev mat (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

theorem mat_injective : Function.Injective (mat ε) := fun _ _ h => Subtype.ext (Units.ext h)

def rep (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (x : Matrix (Fin n) (Fin n) ℂ) : X →L[ℂ] X := by
  classical exact if h : ∃ g, mat ε g = x then π h.choose else 1

theorem rep_mat (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (g : Formalism.REAL.UJ ε) : rep ε π (mat ε g) = π g := by
  have h : ∃ g', mat ε g' = mat ε g := ⟨g, rfl⟩
  rw [rep, dite_eq_left h, mat_injective ε h.choose_spec]

theorem range_mat : Set.range (mat ε) = Formalism.MainNotions.S.UJset ε := (Formalism.REAL.isClosedEmbeddingMatrix n ε).2

theorem mat_mem (g : Formalism.REAL.UJ ε) : mat ε g ∈ Formalism.MainNotions.S.UJset ε := range_mat ε ▸ ⟨g, rfl⟩

theorem exists_mat {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ Formalism.MainNotions.S.UJset ε) : ∃ g, mat ε g = x := by
  rw [← range_mat ε] at hx; exact hx

theorem isEmbedding_mat : Topology.IsEmbedding (mat ε) := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding

end GlobalTheory.PsCo.PcEF.MatrixRepresentation

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEF.MatrixRepresentation

theorem unitaryRep_upq_matrixFunction : MatRep := by
  intro n ε U _ _ π hπ hi
  refine ⟨rep ε π, ⟨⟨?_, fun a ha b hb => ?_⟩, fun a ha v => ?_, fun v => ?_⟩, fun S hS hinv => ?_, fun g => rep_mat ε π g⟩
  · have h1 : mat ε 1 = 1 := rfl
    rw [← h1, rep_mat, map_one]
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    obtain ⟨h, rfl⟩ := exists_mat ε hb
    have hm : mat ε g * mat ε h = mat ε (g * h) := rfl
    rw [hm, rep_mat, rep_mat, rep_mat, map_mul]
    rfl
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    rw [rep_mat]
    exact hπ.norm_apply g v
  · have hr : Formalism.MainNotions.S.UJset ε = Set.range (mat ε) := (range_mat ε).symm
    show ContinuousOn (fun g => rep ε π g v) (Formalism.MainNotions.S.UJset ε)
    rw [hr, continuousOn_iff_continuous_domRestrict]
    let E := (isEmbedding_mat ε).toHomeomorph
    have hE : ∀ y, (fun g => π g v) (E.symm y) = rep ε π (y : Matrix (Fin n) (Fin n) ℂ) v := by
      intro y
      obtain ⟨g, rfl⟩ := E.surjective y
      show π (E.symm (E g)) v = rep ε π (mat ε g) v
      rw [E.symm_apply_apply, rep_mat]
    exact ((hπ.continuous_apply v).comp E.symm.continuous).congr hE
  · exact hi.2 S ⟨hS, fun g v hv => by simpa [rep_mat] using hinv _ (mat_mem ε g) v hv⟩

end GlobalTheory.PsCo.PcEF

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetBlocks
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
open GlobalTheory.SplitFlip (omA omB invT IsUnif mem_KO_iff isOpen_KO)
open GlobalTheory.StdLocZeta (StdSupp stdDatum)
open GlobalTheory.StdLoc (glVol blockIdx)
open scoped NNReal ENNReal

noncomputable section

attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.LocStd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Renumber

variable {X a b a' b' : Type} [Fintype a] [Fintype b] [Fintype a'] [Fintype b'] [MeasurableSpace X]

end Renumber

section Level

variable {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

theorem mem_image_KO {M : Matrix D D k} :
    M ∈ Units.val '' (KO k D : Set (GL D k)) ↔ (∀ i j, M i j ∈ 𝒪[k]) ∧ valuation k M.det = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨((mem_KO_iff g).1 hg).1, SplitFlip.valuation_gdet_of_mem_KO hg⟩
  · rintro ⟨hM, hd⟩
    let N : Matrix D D 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
    have e : (algebraMap 𝒪[k] k).mapMatrix N = M := rfl
    have hu : IsUnit N.det := by
      refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
      rw [RingHom.map_det, e, hd]
    obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det N).2 hu
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    change (algebraMap 𝒪[k] k).mapMatrix u.val = M
    rw [hu', e]

theorem mem_KO_iff_det {g : GL D k} : g ∈ KO k D ↔ (∀ i j, g.val i j ∈ 𝒪[k]) ∧ valuation k g.val.det = 1 := by
  rw [← mem_image_KO]
  exact ⟨fun h => ⟨g, h, rfl⟩, fun ⟨u, hu, e⟩ => Units.ext e ▸ hu⟩



variable {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (σ : A ⊕ A' ≃ D)

variable [MeasurableSpace k] [BorelSpace k]

end Level

section Pair

variable {n n' : ℕ} {D : Type} [Fintype D] [DecidableEq D]

def colDatum (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (σ : Fin n ⊕ Fin n' ≃ D) (X : Matrix (Fin n) D k) : ℂ :=
  stdDatum ν ϖ c (Xᵀ.submatrix σ id)

variable (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (σ : Fin n ⊕ Fin n' ≃ D)


omit [Fintype D] [DecidableEq D] in
theorem colDatum_eq {X : Matrix (Fin n) D k} {u : GL (Fin n) k} (hu : u ∈ KO k (Fin n))
    (h₁ : ∀ i j, X i (σ (.inl j)) = u.val i j) (h₂ : ∀ i j, X i (σ (.inr j)) ∈ cball (ϖ ^ c)) :
    colDatum ν ϖ c σ X = (((ν (GeneralLinearGroup.det u))⁻¹ : ℂˣ) : ℂ) := by
  have e : (Xᵀ.submatrix σ id).toRows₁ = u.valᵀ := by ext i j; exact h₁ j i
  have h : StdSupp ϖ c (Xᵀ.submatrix σ id) :=
    ⟨fun i j => by rw [e]; exact (mem_KO_iff_det.1 hu).1 j i, by rw [e, det_transpose]; exact (mem_KO_iff_det.1 hu).2,
      fun i j => h₂ j i⟩
  rw [colDatum, stdDatum, dite_eq_left h]
  congr 3
  exact Units.ext (by simp [e])

variable [MeasurableSpace k] [BorelSpace k] {m : Measure k}

variable {ν ϖ}


end Pair

section Main

variable {a a' : ℕ} {D : Type} [Fintype D] [DecidableEq D]

end Main

section Place

open IsDedekindDomain NumberField GlobalTheory.CMVal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end Place

end GlobalTheory.LocStd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeCoordHyp
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mem_offHyp_iff {n : ℕ} {S : Finset (Fin n)}
    {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n} :
    v ∈ _root_.GlobalTheory.GoodTop.offHyp S U ↔ v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0 := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  exact Iff.rfl


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
lemma _root_.GlobalTheory.GoodTop.offHyp_ae_eq {n : ℕ} (S : Finset (Fin n))
    (U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) : _root_.GlobalTheory.GoodTop.offHyp S U =ᵐ[volume] U := by
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · exact measure_mono_null
      (fun v hv => (hv.2 (mem_offHyp_iff.1 hv.1).1).elim) measure_empty
  · refine measure_mono_null (t := ⋃ a ∈ (S : Set (Fin n)), {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a = 0})
      ?_ ?_
    · intro v hv
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, exists_prop]
      by_contra h
      push_neg at h
      exact hv.2 (mem_offHyp_iff.2 ⟨hv.1, h⟩)
    · refine (measure_biUnion_null_iff S.countable_toSet).2 fun a _ => ?_
      let L : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℝ] ℂ :=
        (EuclideanSpace.proj a : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).toLinearMap.restrictScalars ℝ
      have hset : {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a = 0} = (LinearMap.ker L : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) := by
        ext v
        simp [L]
      rw [hset]
      refine Measure.addHaar_submodule _ _ fun htop => ?_
      have hmem : EuclideanSpace.single a (1 : ℂ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
      simp [L] at hmem

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilUniq

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_om_inv (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om p⁻¹ f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem om_inv_om (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p⁻¹ (om p f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_scalar (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') (p : GA D S × GA D T) :
    ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → om p f = (c : ℂ) • om' p f := by
  obtain ⟨c, hc, h⟩ := _root_.GlobalTheory.ThetaSchur.schur D ψ H.std S T (om' p⁻¹ * om p)
    (fun f hf => H'.om_pres _ _ (H.om_pres _ _ hf))
    (fun w f hf => by
      obtain ⟨g, h⟩ := p
      have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at e
      rw [Module.End.mul_apply, Module.End.mul_apply, H.om_heis g h w f hf, Prod.inv_mk,
        H'.om_heis _ _ _ _ (H.om_pres _ _ hf), e])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, H'.om_unit μ 𝓕 hμ h𝓕 _ _ (H.om_pres _ _ hf), H.om_unit μ 𝓕 hμ h𝓕 _ _ hf])
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, fun f hf => ?_⟩
  have := congrArg (om' p) (h f hf)
  rwa [Module.End.mul_apply, om_om_inv, map_smul] at this

theorem exists_ne_zero_at_zero (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) :
    ∃ f₀, IsThetaFunO ψ S T f₀ ∧ f₀ 0 ≠ 0 := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h0
  refine ⟨heisO ψ S T w f, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w, ?_⟩
  unfold heisO
  rw [zero_add]
  refine mul_ne_zero ?_ hw
  exact (ψ.val_isUnit _).ne_zero

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := by
  intro i j
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem scalar_split (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') {e : AE D}
    (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {c : Circle}
    (hc : ∀ f, IsThetaFunO ψ S T f → om (g, h) f = (c : ℂ) • om' (g, h) f) : c = 1 := by
  obtain ⟨x, hx⟩ := exists_isDetAt he.1 S g
  obtain ⟨y, hy⟩ := exists_isDetAt he.1 T h
  obtain ⟨r, hr, h1⟩ := H.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', h2⟩ := H'.om_split e he g h hg hh x y hx hy
  obtain ⟨ℓ, hℓ, f, hf, hne⟩ := _root_.GlobalTheory.HalfCoinv.exists_invariant_form D ψ H.std S T e he
  have e1 := h1 ℓ hℓ f hf
  rw [hc f hf, map_smul, h2 ℓ hℓ f hf, smul_eq_mul] at e1
  have e2 : (c : ℂ) * r' = r := by
    apply mul_right_cancel₀ (mul_ne_zero (Circle.coe_ne_zero (splitFacO χS χT x y)) hne)
    linear_combination e1
  have e3 : r' = r := by
    have := congrArg norm e2
    rwa [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Real.norm_of_nonneg hr'.le] at this
  subst e3
  apply Circle.ext
  apply mul_right_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne')
  rw [e2, Circle.coe_one, one_mul]

theorem weilDatum_unique : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om om' : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f := by
  intro D ψ hψ S T χS χT om om' H H' p f hf
  by_cases h0 : f = 0
  · rw [h0, map_zero, map_zero]
  obtain ⟨f₀, hf₀, h00⟩ := exists_ne_zero_at_zero hψ hf h0
  have hne : ∀ q, om' q f₀ ≠ 0 := fun q hq => by
    have := om_inv_om om' q f₀
    rw [hq, map_zero] at this
    exact h00 (by rw [← this]; rfl)
  choose c hc using exists_scalar H H'
  have hmul : ∀ q q', c (q * q') = c q * c q' := fun q q' => by
    apply Circle.ext
    apply smul_left_injective ℂ (hne (q * q'))
    have := hc (q * q') f₀ hf₀
    dsimp only
    rw [← this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc q' f₀ hf₀, map_smul,
      hc q _ (H'.om_pres _ _ hf₀), smul_smul, Circle.coe_mul, mul_comm]
  have hcont : Continuous c := by
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun q => ?_)
    obtain ⟨w, hw⟩ := Function.ne_iff.1 (hne q)
    have h1 : ContinuousAt (fun q' => om q' f₀ w / om' q' f₀ w) q :=
      (H.om_cont f₀ hf₀ w).continuousAt.div (H'.om_cont f₀ hf₀ w).continuousAt hw
    refine h1.congr ?_
    filter_upwards [(H'.om_cont f₀ hf₀ w).continuousAt.eventually_ne hw] with q' hq'
    rw [hc q' f₀ hf₀, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hq']
    rfl
  have hrat : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, c (γ, γ') = 1 := fun γ hγ γ' hγ' => by
    have h1 := congrFun (hc (γ, γ') f₀ hf₀) 0
    rw [Pi.smul_apply, H.om_aut γ hγ γ' hγ' f₀ hf₀, H'.om_aut γ hγ γ' hγ' f₀ hf₀, smul_eq_mul] at h1
    apply Circle.ext
    apply mul_right_cancel₀ h00
    rw [← h1, Circle.coe_one, one_mul]
  let ν : GA D S × GA D T →* Circle := MonoidHom.mk' c hmul
  have hS := _root_.GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D S (ν.comp (MonoidHom.inl _ _)) (hcont.comp (Continuous.prodMk_left _))
    (fun γ hγ => hrat γ hγ 1 (one_mem _))
    (fun e he g hg => scalar_split H H' he hg (suppAt_one e T) (hc (g, 1)))
  have hT := _root_.GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D T (ν.comp (MonoidHom.inr _ _)) (hcont.comp (Continuous.prodMk_right _))
    (fun γ hγ => hrat 1 (one_mem _) γ hγ)
    (fun e he h hh => scalar_split H H' he (suppAt_one e S) hh (hc (1, h)))
  have h1 : c p = 1 := by
    have e : p = (p.1, 1) * (1, p.2) := by rw [Prod.mk_mul_mk, mul_one, one_mul]
    rw [e, hmul, show c (p.1, 1) = 1 from hS p.1, show c (1, p.2) = 1 from hT p.2, mul_one]
  rw [hc p f hf, h1, Circle.coe_one, one_smul]

end GlobalTheory.WeilUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylRepInvMulDiag
section
open GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.WeylCell

namespace GlobalTheory.GKFactor

variable {k : Type} [Field k] {n : ℕ}

theorem weylRep_inv_mul_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (p : Fin n) :
    (x⁻¹).val p (w p) * x.val (w p) p = 1 := by
  have h : (x⁻¹ * x).val p p = (1 : GL (Fin n) k).val p p := by rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
  rwa [Finset.sum_eq_single (w p) (fun b _ hb => by rw [hx b p hb, mul_zero]) (by simp)] at h

theorem weylRep_mul_inv_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (p : Fin n) :
    x.val (w p) p * (x⁻¹).val p (w p) = 1 := by
  have h : (x * x⁻¹).val (w p) (w p) = (1 : GL (Fin n) k).val (w p) (w p) := by rw [mul_inv_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
  rwa [Finset.sum_eq_single p (fun b _ hb => by
      rw [hx (w p) b (fun e => hb (w.injective e).symm), zero_mul]) (by simp)] at h

theorem weylRep_inv {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) : IsWeylRep w⁻¹ x⁻¹ := by
  intro p a hpa
  have hne : x.val a (w⁻¹ a) ≠ 0 := by
    intro h0
    have := weylRep_mul_inv_diag hx (w⁻¹ a)
    rw [show w (w⁻¹ a) = a by simp] at this
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have h : (x⁻¹ * x).val p (w⁻¹ a) = (1 : GL (Fin n) k).val p (w⁻¹ a) := by rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_ne hpa] at h
  rw [Finset.sum_eq_single a (fun b _ hb => by
      rw [hx b (w⁻¹ a) (by simpa using hb), mul_zero]) (by simp)] at h
  exact (mul_eq_zero.1 h).resolve_right hne

theorem weylRep_conj_apply {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (u : GL (Fin n) k)
    (p q : Fin n) : (x⁻¹ * u * x).val p q = (x⁻¹).val p (w p) * u.val (w p) (w q) * x.val (w q) q := by
  have hi := weylRep_inv hx
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (w q)
    (fun b _ hb => by rw [hx b q hb, mul_zero]) (by simp), Matrix.mul_apply,
    Finset.sum_eq_single (w p) (fun b _ hb => by rw [hi p b (fun e => hb (by rw [e]; simp)), zero_mul]) (by simp)]

theorem mem_cell_iff {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (u : GL (Fin n) k) :
    u ∈ cell x ↔ u ∈ unipB k (Fin n) ∧ ∀ a b, a < b → w⁻¹ a < w⁻¹ b → u.val a b = 0 := by
  rw [mem_cell, mem_unipBLower]
  refine and_congr_right fun hu => ?_
  rw [mem_unipB] at hu
  constructor
  · rintro ⟨hl, -⟩ a b hab hw
    have h := hl _ _ hw
    rw [weylRep_conj_apply hx, show w (w⁻¹ a) = a by simp, show w (w⁻¹ b) = b by simp] at h
    have h1 := weylRep_inv_mul_diag hx (w⁻¹ a)
    have h2 := weylRep_mul_inv_diag hx (w⁻¹ b)
    rw [show w (w⁻¹ a) = a by simp] at h1
    rw [show w (w⁻¹ b) = b by simp] at h2
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rw [h, zero_mul] at h1; exact absurd h1 zero_ne_one
      · exact h
    · rw [h, zero_mul] at h2; exact absurd h2 zero_ne_one
  · intro h
    refine ⟨fun p q hpq => ?_, fun p => ?_⟩
    · rw [weylRep_conj_apply hx]
      rcases lt_or_gt_of_ne (fun e : w p = w q => hpq.ne (w.injective e)) with hl | hl
      · rw [h _ _ hl (by simpa using hpq), mul_zero, zero_mul]
      · rw [hu.1 _ _ hl, mul_zero, zero_mul]
    · rw [weylRep_conj_apply hx, hu.2, mul_one, weylRep_inv_mul_diag hx]

end GlobalTheory.GKFactor
end

