module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.CompatCsdOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ProModOfCtx2OfKPairOfStar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0041
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.Narrow
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.UnlAllOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWitApi

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutCsdIso
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base
namespace UpperTheory.GalN.V
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}
theorem autCsd_iso_alt {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.RepIso r r')
    (H : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r) : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r' :=
  ⟨H.1.imp fun _ k => ⟨k.1, k.2.1, attC_iso h k.2.2⟩, fun c => (H.2 (continuous_of_iso c h.symm')).isobaricDense h⟩
end
def AutomorphyOverRationalsIsobaricDense : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → _root_.UpperTheory.V.Z.Win.IsAutQA ι r' → _root_.UpperTheory.V.Z.Win.IsAutQA ι r
theorem autQIsoN : _root_.UpperTheory.GalN.V.AutomorphyOverRationalsIsobaricDense := by
  intro F Ω _ _ _ _ l _ ι n r r' e h hc K _ _ _ _ _ _ h2 hi
  let φ : G K Ω →* G F Ω := AlgEquiv.restrictScalarsHom F
  have e' : RepIso (r.comp φ) (r'.comp φ) :=
    e.imp fun _ hg s => hg _
  have hi' : IsIrr (r'.comp φ) := by
    obtain ⟨g, hg⟩ := e'
    refine ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
    let T := Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) (Qbar l))
    have hcomm (s : G K Ω) : g * (r.comp φ) s = (r'.comp φ) s * g := by
      rw [hg s, inv_mul_cancel_right]
    have hcomap := hi.2.2 (W.comap T) le_top (fun s v hv => by
      change T ((↑((r.comp φ) s) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) ∈ W
      dsimp only [T]
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, hcomm,
        Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hW s (T v) hv)
    have hsurj : Function.Surjective T := fun v =>
      ⟨(↑(g⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v, by
        dsimp only [T]
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.one_mulVec]⟩
    have hmap := Submodule.map_comap_eq_of_surjective hsurj W
    rcases hcomap with hbot | htop
    · left
      rw [← hmap, hbot, Submodule.map_bot]
    · right
      rw [← hmap, htop, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  obtain ⟨⟨π, h1, h3⟩, hw⟩ := h (continuous_of_iso hc e) K h2 hi'
  exact ⟨⟨π, h1, attC_iso e'.symm' h3⟩, hw.isobaricDense e'.symm'⟩
end UpperTheory.GalN.V
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthSeedII
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
section
variable {l : ℕ} [Fact l.Prime]
private theorem lt_add {a b : Qbar l} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)
private theorem norm_of_cong {a b : Qbar l} (h : ‖a - b‖ < 1) (hb : ‖b‖ = 1) : ‖a‖ = 1 := by
  have e : a = (a - b) + b := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hb]; exact h.ne), hb, max_eq_right h.le]
private theorem root_ex {a : Qbar l} (ha : ‖a - 1‖ < 1) {z : (Qbar l)ˣ} (hz : Cong z 1 ∨ Cong z (-1)) :
    ∃ α : (Qbar l)ˣ, (α : Qbar l) ^ 2 = a ∧ Cong α z := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq a two_pos
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [← hx] at ha
    simp at ha
  have h1 : ∃ y : Qbar l, y ≠ 0 ∧ y ^ 2 = a ∧ ‖y - 1‖ < 1 := by
    have e : ‖x - 1‖ * ‖-x - 1‖ < 1 := by
      rw [← norm_mul, show (x - 1) * (-x - 1) = -(a - 1) by rw [← hx]; ring, norm_neg]
      exact ha
    by_cases h : ‖x - 1‖ < 1
    · exact ⟨x, hx0, hx, h⟩
    · refine ⟨-x, neg_ne_zero.2 hx0, by rw [← hx]; ring, ?_⟩
      nlinarith [norm_nonneg (-x - 1), not_lt.1 h]
  obtain ⟨y, hy0, hy, hy1⟩ := h1
  rcases hz with hz | hz
  · refine ⟨Units.mk0 y hy0, hy, ?_⟩
    have := lt_add hy1 (by rw [norm_neg]; exact hz : ‖-((z : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l))‖ < 1)
    simpa [Cong] using this
  · refine ⟨-Units.mk0 y hy0, by simpa using hy, ?_⟩
    have := lt_add hy1 hz
    rw [← norm_neg] at this
    have e : ((-Units.mk0 y hy0 : (Qbar l)ˣ) : Qbar l) - z = -(y - 1 + ((z : Qbar l) - ((-1 : (Qbar l)ˣ) : Qbar l))) := by
      rw [Units.val_neg, Units.val_neg, Units.val_mk0, Units.val_one]
      ring
    rw [Cong, e]
    exact this
end
private theorem indEx (hP : MixOfP) :
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    D.Good → T.Ok → T.Two → T.Deep → ∀ ι : Qbar l ≃+* ℂ,
    ∃ (k₀ : IntermediateField ℚ Ω) (_ : NumberField k₀) (_ : IsTotallyReal k₀) (φ : G ℚ Ω →* (Qbar l)ˣ) (k t : ℕ)
      (r : G k₀ Ω →* GL (Fin 2) (Qbar l)) (α β : (Qbar l)ˣ) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) (δ : G T.F Ω →* (Qbar l)ˣ),
      IndDat T k₀ φ ι k t r α β R δ ∧ PR ι r := by
  intro Ω _ _ _ l _ c D T hg hok h2 hd ι
  obtain ⟨k₀, _, _, φ, hyp, hrange, hidx, hemb⟩ := UpperTheory.exists_quadratic_character_of_subgroup_index_two Ω l c D T hg hok h2 hd
  have hc := UpperTheory.galois_character_residual_decomposition Ω l c D T k₀ φ hyp
  obtain ⟨k, t, r₀, dat₀, hrw⟩ := hP Ω l c D T k₀ φ ι hyp hc
  obtain ⟨u, hu⟩ : resQ T.F T.g0 * resQ T.F T.g0 ∈ (resQ k₀).range := hrange ▸ Subgroup.mul_self_mem_of_index_two hidx _
  obtain ⟨r, iso, h01, h10, rib, ns⟩ := UpperTheory.exists_ribet_lattice Ω l c D T k₀ φ ι k t r₀ hyp hc dat₀ u hu
  have dat := UpperTheory.galoisRep_properties_invariant_under_conjugation Ω l k₀ ι _ k t r₀ r dat₀ iso
  set μ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ k * up D.ξ * φ with hμ
  have hF : ∀ g : G T.F Ω, resQ T.F g ∈ T.F.fixingSubgroup := fun g => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => g.commutes ⟨x, hx⟩
  have hdet : ∀ h, Matrix.GeneralLinearGroup.det (r h) = μ (resQ k₀ h) := fun h => by
    have e := DFunLike.congr_fun dat.det h
    have e' : φ (resQ k₀ h) = 1 := hyp.φ_in _ (hrange ▸ ⟨h, rfl⟩)
    simp only [hμ, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, e', mul_one] at e ⊢
    rw [e]
    rfl
  have ru := rib u (by rw [hu, ← map_mul]; exact hF _)
  obtain ⟨α, hα, hαc⟩ := root_ex ru.1 hc.c3
  have hmu := hc.mult k dat.dvd
  have hμ1 : ∀ g : G T.F Ω, ‖(μ (resQ T.F g) : Qbar l)‖ = 1 := fun g =>
    norm_of_cong (by rw [norm_sub_rev]; exact hmu g) (hc.unit _ _)
  have hα1 : ‖(α : Qbar l)‖ = 1 := norm_of_cong hαc (hc.unit _ _)
  obtain ⟨R, hR, hgsp⟩ := UpperTheory.symmetric_square_mixed_exists (Qbar l) _ _ (resQ k₀) (resQ T.F T.g0) α (μ (resQ T.F T.g0) / α) r μ two_ne_zero
    hemb.injective (hrange ▸ hidx) (hrange ▸ hc.out) (fun u' hu' => by
      obtain rfl : u' = u := hemb.injective (hu'.trans hu.symm)
      have e := congrArg Units.val (hdet u')
      rw [hu, map_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h01, h10, ← hα, Units.val_mul] at e
      ext i j
      fin_cases i <;> fin_cases j
      · simp [hα]
      · simp [h01]
      · simp [h10]
      · have := α.ne_zero
        simp only [Fin.mk_one, Fin.isValue, Matrix.diagonal_apply_eq, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          Units.val_div_eq_div_val]
        field_simp
        linear_combination e) hdet (mul_div_cancel _ _)
  have hres : Continuous (resQ T.F) := (emb ℚ T.F Ω).continuous
  obtain ⟨δ, hδc, hδ2, hδ1⟩ := UpperTheory.exists_square_root_of_character_near_one l hg.l_odd _ ((up D.th / μ).comp (resQ T.F)) ((hc.cont k).comp hres) fun g => by
    have := (μ (resQ T.F g)).ne_zero
    have e : (((up D.th / μ).comp (resQ T.F) g : (Qbar l)ˣ) : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) =
        ((up D.th (resQ T.F g) : Qbar l) - μ (resQ T.F g)) / μ (resQ T.F g) := by
      rw [MonoidHom.comp_apply, MonoidHom.div_apply, Units.val_div_eq_div_val, Units.val_one, sub_div, div_self this]
    rw [Cong, e, norm_div, hμ1, div_one]
    exact hmu g
  haveI : FaithfulSMul k₀ Ω := (faithfulSMul_iff_algebraMap_injective k₀ Ω).2 (algebraMap k₀ Ω).injective
  haveI : Module.IsTorsionFree k₀ Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  refine ⟨k₀, ‹_›, ‹_›, φ, k, t, r, α, _, R, δ, ⟨hyp, hc, dat, rib, ns, hR,
    UpperTheory.continuous_mix_family l _ _ _ _ _ _ r R hR hemb dat.cont, hgsp, hαc, ?_, hδc, fun g => ?_, hδ1⟩, prIso k₀ Ω l ι 2 r₀ r iso hrw⟩
  · have e0 := congrArg Units.val (hc.mul 0 (resQ T.F T.g0))
    have := α.ne_zero
    have e : ((μ (resQ T.F T.g0) / α : (Qbar l)ˣ) : Qbar l) - ch T 0 (resQ T.F T.g0) =
        (-((up D.th (resQ T.F T.g0) : Qbar l) - μ (resQ T.F T.g0)) +
          -(ch T 0 (resQ T.F T.g0) * ((α : Qbar l) - ch T 3 (resQ T.F T.g0)))) / α := by
      rw [← e0, Units.val_div_eq_div_val, Units.val_mul, show (0 : Fin 4).rev = 3 from rfl]
      field_simp
      ring
    rw [Cong, e, norm_div, hα1, div_one]
    refine lt_add (by rw [norm_neg]; exact hmu _) ?_
    rw [norm_neg, norm_mul, hc.unit, one_mul]
    exact hαc
  · rw [hδ2, MonoidHom.comp_apply, MonoidHom.div_apply, div_mul_cancel]
theorem UpperTheory.V.Z.Bc.seedII_of_p_alt :
    MixOfP → IndAutLP → _root_.UpperTheory.V.Ws.SeedIIAlt := by
  intro hP hI Ω _ _ _ l _ c D T hctx hok h2 hd ι
  obtain ⟨k₀, _, _, φ, k, t, r, α, β, R, δ, h, hrw⟩ := indEx hP Ω l c D T hctx.1 hok h2 hd ι
  have hirr : IsIrr ((R.comp (resQ T.F)).comp T.G'.subtype) := UpperTheory.induced_irreducible Ω l c D T k₀ φ ι k t r α β R δ h
  obtain ⟨n, hloc, m, b, N, hm, hw, hN, hfin⟩ := indLoc0 Ω l c D T k₀ φ ι k t r α β R δ h
  obtain ⟨⟨π, hreg, hatt⟩, hW⟩ := hI Ω l c D T k₀ φ ι k t r α β R δ h hrw
  refine _root_.UpperTheory.induced_final_statement_alt Ω l c D T ι ⟨twF T R δ, n⟩ (indGlob_of_kill UpperTheory.induced_representation_constituent_vanishing Ω l c D T k₀ φ ι k t r α β R δ h) hloc ⟨?_, ?_⟩
  · rw [(irrIff _).1]
    have := (shapeFacts l _ 4 _ (δ.comp T.G'.subtype)).2.2.2.2.2 hirr
    convert this using 1
    ext g : 2
    rfl
  · have hcont : Continuous (resLe T.F_le) := by
      rw [(emb ℚ T.F Ω).continuous_iff]
      exact (emb ℚ T.L Ω).continuous
    refine ⟨fun i => 2 * m i + b, (δ.comp (resLe T.F_le))⁻¹, π, -b, N, fun i => ⟨m i.castSucc - m i.succ, by linarith [hm i], by ring⟩,
      hw, (h.δ_cont.comp hcont).inv, hN, ⟨m 0, by ring⟩, fun A _ s _ => ?_, _root_.UpperTheory.V.Z.Win.Birth.mkReg' hreg (hW π hreg hatt), ?_⟩
    · have e := hfin (resLe T.F_le s)
      have e' : cycBar T.L Ω l s = cycBar T.F Ω l (resLe T.F_le s) := rfl
      rw [← inv_eq_one, ← inv_pow, ← e, e']
      simp [mul_comm]
    · convert hatt using 1
      ext g : 2
      rw [tw_val]
      change _ • (tw (R.comp (resQ T.F)) δ (resLe T.F_le g)).val = _
      rw [tw_val, smul_smul]
      simp
      rfl
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuspUnique
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol
namespace UpperTheory.V.Z.Bc
private theorem cusp_unique {F : Type} [Field F] [NumberField F] {n : ℕ} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    {inf : (F →+* ℂ) → Multiset ℂ → Prop} (h : IsCusp n sat inf) : ∀ v B B', sat v B → sat v B' → B = B' := by
  rcases h with ⟨_, π, rfl, -⟩ | ⟨_, π, rfl, -⟩
  · exact fun _ _ _ h h' => h.unique h'
  · exact fun _ _ _ h h' => h.unique h'
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)
theorem stepC_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (cyc : CycC) : StepC := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hp hK hM l _ ι n hn r hr hirr hpol
  obtain ⟨hup, hdown, -⟩ := cyc K M hp inferInstance n hn
  have hss : IsSSRep (r.comp (resG K M Ω)) := (Bc.irrBasic.1 _ Unit _ n _).2.1 hirr
  have hirr' : IsIrr r := (Bc.irrBasic.1 _ _ _ n r).1 _ hirr
  have hcont := continuous_restrictScalarsHom K M Ω
  constructor
  · rintro ⟨sat, inf, hc, hreg, hatt⟩
    rcases hup sat inf hc hreg with ⟨η, hη, ht⟩ | ⟨sat', inf', hc', hbc, hinf⟩
    · obtain ⟨δ, h1, -, h2, h3⟩ := _root_.UpperTheory.V.Sd.self_twist_galois_of_printed_results H.toClassicalTheorems K Ω l ι n r sat (cusp_unique hc) hr hatt η _ hp.pos hη.2.1 hη.1 ht
      exact (h1 (UpperTheory.schur_twist_holds _ _ _ n r (resG K M Ω) δ hirr (h3 M hη) h2)).elim
    · refine ⟨sat', inf', hc', fun τ => ?_, UpperTheory.satake_base_change_attached K M Ω l ι n r sat sat' (cusp_unique hc) hbc hatt hss⟩
      obtain ⟨m, hm, h⟩ := hreg (τ.comp (algebraMap K M))
      exact ⟨m, hinf τ m hm, h⟩
  · rintro ⟨sat', inf', hc', hreg', hatt'⟩
    obtain ⟨sat, inf, hc, hbc, hinf⟩ := hdown sat' inf' hc' hreg' (UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic UpperTheory.frobenius_conj_of_galois_conjugate_places UpperTheory.hecke_eigenvalue_basic_properties K M Ω l ι n r sat' hatt')
    have hreg : RegInf n inf := fun τ => by
      obtain ⟨m, hm, h⟩ := hreg' (ComplexEmbedding.lift M τ)
      have := hinf _ m hm
      rw [ComplexEmbedding.lift_comp_algebraMap] at this
      exact ⟨m, this, h⟩
    obtain ⟨r₁, hr₁, hatt₁⟩ := (show ∃ r₁ : G K Ω →* GL (Fin n) (Qbar l), Continuous r₁ ∧ AttachedSys ι r₁ sat by
      rcases hc with ⟨hC, π, rfl, rfl⟩ | ⟨hR, -⟩
      · refine _root_.UpperTheory.V.Z.Bc.exDownC_sv_alt H cyc K M Ω hp l ι n hn r π sat' inf' hpol ((GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_) hc' hbc hatt'
        obtain ⟨m, hm, h⟩ := hreg τ
        rw [CG.HasInfChar.infChar_eq (π := CG.mk π) hm]
        exact h
      · exact (not_both K hR inferInstance).elim)
    have hN := (UpperTheory.galois_representation_image_spec K M Ω).1
    have hss₁ := UpperTheory.semisimpleModule_restriction_to_normal_subgroup _ _ _ n r₁ (resG K M Ω) hN hatt₁.1
    have hatt₁' := UpperTheory.satake_base_change_attached K M Ω l ι n r₁ sat sat' (cusp_unique hc) hbc hatt₁ hss₁
    have hiso : RepIso (r₁.comp (resG K M Ω)) (r.comp (resG K M Ω)) := by
      refine _root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results H.toClassicalTheorems M Ω l ι n _ _ (hr₁.comp hcont) (hr.comp hcont) hss₁ hss ?_
      filter_upwards [hatt₁'.2, hatt'.2] with w ⟨B, hB, h⟩ ⟨B', hB', h'⟩
      obtain rfl := cusp_unique hc' w B B' hB hB'
      exact ⟨_, h, h'⟩
    obtain ⟨δ, hδ, hiso'⟩ := UpperTheory.schur_extension _ _ _ n r r₁ (resG K M Ω) hN hirr hiso
    have hF := UpperTheory.finiteCharacter_of_algebraic_cyclotomic (_root_.UpperTheory.V.Af.algOfCyc_s H)
    obtain ⟨sat₂, inf₂, hc₂, hreg₂, hatt₂⟩ := _root_.UpperTheory.V.Af.twist_invariance_automorphic H K Ω l ι n r₁ δ ⟨sat, inf, hc, hreg, hatt₁⟩
      (hF.1 K Ω l ι δ (hF.2 K M Ω l δ hδ))
    exact ⟨sat₂, inf₂, hc₂, hreg₂, (Bc.irrBasic.1 _ Unit _ n _).2.1 hirr',
      hatt₂.2.mono fun w ⟨B, hB, h⟩ => ⟨B, hB, h.of_iso hiso'⟩⟩
theorem solC_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (cyc : CycC) : SolE := solC_of_stepC (_root_.UpperTheory.V.Z.Bc.stepC_alt H cyc)
end UpperTheory.V.Z.Bc
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Gsp4PromodularityCaseTwo
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
private theorem conj_trans {H R : Type} [Group H] [CommRing R] {r r' r'' : H →* M4 R} (h : IsConj4 r r') (h' : IsConj4 r' r'') :
    IsConj4 r r'' := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := h'
  exact ⟨v * u, fun g => by rw [hv, hu, mul_inv_rev, Units.val_mul, Units.val_mul]; simp only [mul_assoc]⟩
private theorem res_self (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] :
    (res O O : O →+* ResidueField O) = residue O := RingHom.ext fun x => (res O O).commutes x
private theorem last_step (hC : CohomologyHyp) (hPM : _root_.UpperTheory.V.Ws.PMExAlt) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} {D : Raw Ω c} (T : Tower D) (hF : T.Fit) (hD : T.Deep) (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (C : ℕ)
    (hB : ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → (T.fr ∅).Bounds a T.d C)
    (hd : 30 * (C + 1) * (C + 1) ≤ T.d) {c₁ : Coef l} {h₁ : c.O ≤ c₁.O} {Q : PD T.ι (G T.F Ω) c₁.O} (hQ : T.SeedPairAlt ι h₁ Q)
    {P : PD T.ι (G T.F Ω) 𝔞.V} (hs : 𝔞.Small P) (hp : (T.fr ∅).IsPair (𝔞.a c) P)
    (hr : (T.fr ∅).IsRes (𝔞.red c) (P.map (residue 𝔞.V)))
    (hch : (T.fr ∅).Chain (𝔞.red c) (P.map (residue 𝔞.V)) (Q.map (𝔞.red c₁))) :
    ∃ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) (y : X.A →+* 𝔞.V), T.PotentialModularityTower ι X J ∧
      y.comp (algebraMap c'.O X.A) = 𝔞.a c' ∧ (∀ b ∈ maximalIdeal X.B, y (algebraMap X.B X.A b) ∈ maximalIdeal 𝔞.V) ∧
      (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) ∧ X.P.map y = P := by
  obtain ⟨c₂, k₂⟩ := chainDesc 𝔞 c (T.fr ∅) _ _ hr hch
  obtain ⟨c₃, k₃⟩ := smallCo 𝔞 P hs
  obtain ⟨c₄, k₄⟩ := hPM Ω l c D T hF hD ι
  obtain ⟨d₁, a₁, a₂⟩ := (coefSup l).1 c₁ c₂
  obtain ⟨d₂, a₃, a₄⟩ := (coefSup l).1 c₃ c₄
  obtain ⟨c', b₁, b₂⟩ := (coefSup l).1 d₁ d₂
  have e₁ : c₁.O ≤ c'.O := a₁.trans b₁
  have h : c.O ≤ c'.O := h₁.trans e₁
  haveI : Finite (ResidueField c'.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c'.O) := (dvrFacts l c'.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  have hS := (std hC D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  obtain ⟨X⟩ := spaceEx (T.fr ∅) l (inc h) hS
  obtain ⟨J, hJ⟩ := k₄ c' h (a₄.trans b₂) X
  obtain ⟨s, t, es, et, rs, cst⟩ := k₂ c' h (a₂.trans b₁)
  obtain ⟨R, _, _, _, f, QR, fi, fa, fr, qc, rfl⟩ := k₃ c' (a₃.trans b₂)
  have inj := (chainMap (T.fr ∅) ((residue c'.O).comp (inc h)) (𝔞.j c') s).2.2
  have loc : ∀ {d : Coef l} (e : d.O ≤ c'.O), maximalIdeal d.O ≤ (maximalIdeal c'.O).comap (inc e) := fun {d} e x hx hu => by
    have h2 : IsUnit (𝔞.a d x) := 𝔞.compat d c' e x ▸ hu.map (𝔞.a c')
    exact hx (IsLocalHom.map_nonunit x h2)
  have jc : (𝔞.j c').comp ((residue c'.O).comp (inc e₁)) = 𝔞.red c₁ :=
    RingHom.ext fun x => congrArg (residue 𝔞.V) (𝔞.compat c₁ c' e₁ x)
  have lQ : (T.fr ∅).Lifts (inc h) t (Q.map (inc e₁)) := by
    refine ⟨hQ.pair.map (inc e₁), hQ.cont.map _ (loc e₁), inj ?_⟩
    show ((Q.map _).map _).map _ = t.map _
    rw [et, res_self, PD.map_map, PD.map_map, ← jc]
    rfl
  obtain ⟨f₁, hf₁⟩ := X.univ c'.O t _ (Asm.chain_end rs cst).1 lQ
  have sd := hJ.seed ((Algebra.ofId c'.O (PadicAlgCl l)).comp f₁) (by
    have e : X.P.map (((Algebra.ofId c'.O (PadicAlgCl l)).comp f₁ : X.A →ₐ[c'.O] PadicAlgCl l) : X.A →+* PadicAlgCl l) =
        Q.map (algebraMap c₁.O (PadicAlgCl l)) := by
      show (X.P.map (f₁ : X.A →+* c'.O)).map (algebraMap c'.O (PadicAlgCl l)) = _
      rw [hf₁]
      rfl
    rw [e]
    exact hQ.seed)
  have s₁ : X.SomeIn J (RingHom.ker ((res c'.O c'.O).comp f₁)) := Asm.someIn_of_locZero X J _ sd fun z hz => by
    have h0 : f₁ z = 0 := Subtype.ext hz
    show res c'.O c'.O (f₁ z) = 0
    rw [h0, map_zero]
  have e₁' : X.P.map (((res c'.O c'.O).comp f₁ : X.A →ₐ[c'.O] ResidueField c'.O) : X.A →+* ResidueField c'.O) = t := by
    show (X.P.map (f₁ : X.A →+* c'.O)).map (res c'.O c'.O : c'.O →+* ResidueField c'.O) = t
    rw [hf₁]
    exact lQ.red
  have lR : (T.fr ∅).Lifts (inc h) s QR := by
    refine ⟨Asm.pair_of f fi ?_, qc, inj ?_⟩
    · rw [← RingHom.comp_assoc, fa]
      have : (𝔞.a c').comp (inc h) = 𝔞.a c := RingHom.ext fun x => 𝔞.compat c c' h x
      rw [this]
      exact hp
    · show (QR.map _).map _ = s.map _
      rw [es, PD.map_map, PD.map_map, fr]
  obtain ⟨f₀, hf₀⟩ := X.univ R s _ rs lR
  have e₀ : X.P.map (((res c'.O R).comp f₀ : X.A →ₐ[c'.O] ResidueField c'.O) : X.A →+* ResidueField c'.O) = s := by
    show (X.P.map (f₀ : X.A →+* R)).map (res c'.O R : R →+* ResidueField c'.O) = s
    rw [hf₀]
    exact lR.red
  have all := Asm.allIn_of_chain hS X J
    (_root_.UpperTheory.V.Ws.residual_charpoly_rank_four hC D T hF hD ι c' h X J hJ C (hB _ _ fun x hx => (residue_eq_zero_iff _).2 (loc h hx)) hd)
    ((res c'.O R).comp f₀) ((res c'.O c'.O).comp f₁) (e₀ ▸ rs) (e₀ ▸ e₁' ▸ cst) s₁
  refine ⟨c', h, X, J, f.comp (f₀ : X.A →+* R), hJ, ?_, fun b hb => ?_, Asm.zero_of_allIn X J _ all fun z hz => ?_, ?_⟩
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, fa]
  · have h0 : res c'.O R ((f₀.comp (IsScalarTower.toAlgHom c'.O X.B X.A)) b) = 0 := by
      rw [res_map, res_eq_zero_iff]
      exact hb
    refine (residue_eq_zero_iff _).1 ((RingHom.congr_fun fr (f₀ (algebraMap X.B X.A b))).trans ?_)
    exact (congrArg (𝔞.j c') h0).trans (map_zero _)
  · have h0 : f₀ z = 0 := (map_eq_zero_iff f fi).1 hz
    show res c'.O R (f₀ z) = 0
    rw [h0, map_zero]
  · exact congrArg (fun Z => PD.map Z f) hf₀
theorem UpperTheory.V.Ws.proMod_of_pmEx_of_ctx2_of_kPair_of_star :
    CohomologyHyp → UpperTheory.V.Published.FerreroWashington → _root_.UpperTheory.V.Ws.SeedIIAlt → _root_.UpperTheory.V.Ws.PMExAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D →
      ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) → _root_.UpperTheory.V.Ws.ProModAlt D ι 𝔞 r := by
  intro hC hFW h2 hPM Ω _ _ _ l _ c D hD ι 𝔞 r u hK hS
  have hG : D.Good := hD.1
  obtain ⟨pr, hl, hP⟩ := labels D hG 𝔞 r u hK
  obtain ⟨T₀, rfl, ok, two, tame₀⟩ := exists_tame_tower_ok_two D hD pr hl
  have hF₀ : T₀.Fit := ⟨ok, .inl ⟨hD, two⟩⟩
  have hc := _root_.UpperTheory.V.Ws.deep_tower_residue_chain_exists hC h2 D T₀ hD ok two tame₀ ι 𝔞
  obtain ⟨P, qP, nP, cP, sP⟩ := hP _ hF₀.1.dist
  obtain ⟨P', qP', cP', lP'⟩ := lat hC D hG 𝔞 _ _ hl hF₀.1.dist P qP nP (sP hS)
  obtain ⟨T₁, le₁, tame, hT⟩ := hc _ lP'
  have f₁ := leFit D hG T₀ T₁ le₁
  have hF₁ := f₁.2.2.2.2.1 hF₀
  obtain ⟨C, hB⟩ := x2 hC hFW D T₁ hF₁ tame
  obtain ⟨T, m, le, lay, deep, hd⟩ := layerEx D hG T₁ hF₁ tame (30 * (C + 1) * (C + 1))
  have hF := (leFit D hG T₁ T le).2.2.2.2.1 hF₁
  obtain ⟨c₁, h₁, Q, hQ, hch⟩ := hT T le deep
  obtain ⟨P'', sm, pr'', er, ov, rs, ine⟩ := restrQ D hG T₀ T hF₀ (f₁.2.2.2.2.2.2 T le) 𝔞 P' qP' lP'
  obtain ⟨c', h, X, J, y, k1, k2, k3, k4, k5⟩ :=
    last_step hC hPM T hF deep ι 𝔞 C (hB T m le lay) hd hQ sm pr'' rs (hch _ ov rs)
  refine ⟨T, c', h, X, J, y, P'.r, hF, deep, k1, k2, k3, k4, conj_trans cP cP', qP'.pair.mult, by rw [k5, er],
    fun v i s hs => ?_⟩
  subst k5
  exact (PD.map_ψ X.P y v i s).symm.trans (ine v i s hs)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuWrap
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win.Gu
theorem spehOf_alt (H : _root_.UpperTheory.V.Af.HypothesesH') : GlobalTheory.BcSpeh.BcSpeh :=
  _root_.UpperTheory.BaseChangeIdentities.bcSpeh_alt (_root_.UpperTheory.BaseChangeIdentities.bridge H.litN.aut.bc H.litN.loc.bern)
theorem galUnitaryT_of_printsH : _root_.UpperTheory.V.Af.HypothesesH' → GalUnitaryT := fun H => _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH_of_bcSpeh_of_rT H (_root_.UpperTheory.V.Z.Win.Gu.spehOf_alt H) (_root_.UpperTheory.Gal.SV.rowOf' H.litN.aut.gal)
theorem endShape'_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∀ ρ : G E Ω →* GL (Fin n) (Qbar l), Continuous ρ → IsSSRep ρ → (∀ w, IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → LocGlobT ι ρ w τ) → ∃ (a : ℕ) (d m : Fin a → ℕ) (ρ' : ∀ i, G E Ω →* GL (Fin (d i)) (Qbar l)), (∀ i, 1 ≤ d i ∧ 1 ≤ m i ∧ Continuous (ρ' i)) ∧ (∀ g, (UpperTheory.V.W.mat ρ g).charpoly = ∏ i, ∏ j ∈ Finset.range (m i), (UpperTheory.V.W.mat (UpperTheory.V.Af.tw (ρ' i) (cycBar E Ω l ^ (-(j : ℤ)))) g).charpoly) ∧ ((∀ i, m i = 1) → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ b : Multiset ℂ, UpperTheory.V.Af.FrobEig ι ρ w b → ∀ z ∈ b, ∀ z' ∈ b, ‖z‖ < (normV w : ℝ) * ‖z'‖) :=
  fun H => _root_.UpperTheory.V.Z.Win.Gu.endShapeT' H (_root_.UpperTheory.V.Z.Win.Gu.spehOf_alt H) (_root_.UpperTheory.Gal.SV.rowOf' H.litN.aut.gal)
end UpperTheory.V.Z.Win.Gu
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelAdmissibleRestrictionHolds
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr
open UpperTheory.GalN.V
theorem UpperTheory.V.Z.Win.A4.admissible_restriction_level_n_of_printed_results : _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.GalN.V.AdmResNAlt := by
  intro hP K _ _ _ hK n hn m wt hm M hM l _ hl Ω _ _ _ _ _ _ ι r hr hirr
  have hC := Lev.LevelF.of_level hr.level
  have hF := Lev.levelFRes ℚ K Ω l n M m r hC
  obtain ⟨⟨P, hreg, hA⟩, hW⟩ := hr.aut hC.cont K hK hirr
  obtain ⟨θ, hθ, hd⟩ := hr.dual
  obtain ⟨χ, μ, hpol, -, -⟩ := _root_.UpperTheory.V.Z.Bc.polarization_k_of_printed_results hP K hK n (by omega) l Ω ι r wt θ P hθ hd hA
  exact ⟨hirr, ⟨P, hreg, ⟨χ, hpol⟩, hA⟩, hW, hF, _root_.UpperTheory.V.Z.Win.A4.safeRes' K (_root_.UpperTheory.V.Z.Win.A4.safeUP'_alt hP hr.irr hr.level hr.aut hr.safe)⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelZeroEqMaximalCompactAlt
section
noncomputable abbrev UpperTheory.V.Z.Win.WitAQ.weak_admissible_iso := @UpperTheory.GalN.V.WitQ.weak_admissible_iso
end

