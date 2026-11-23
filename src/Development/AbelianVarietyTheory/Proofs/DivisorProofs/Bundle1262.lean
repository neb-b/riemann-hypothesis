module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFrameCharacterFactorization
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CuspRep.UnrSat

theorem eventually_hasSatGL_locRep : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, GlobalTheory.LFun.HasSatGL w (π.locRep w) B := by
  intro hF E _ _ _ a π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  filter_upwards [LocSph.eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))] with w hw
  refine exists_hasSatGL_locRep hF E a π w
    ((Submodule.ne_bot_iff _).2 ⟨⟨φ, hφ⟩, ?_, fun e => h0 (congrArg Subtype.val e)⟩)
  refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext ?_
  obtain ⟨g, rfl⟩ := hk
  exact hw g

end GlobalTheory.CuspRep.UnrSat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterRealExponentEqZeroIffIsUnitary
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem rexp_eq_zero_iff_isUnitary : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Letter E), 1 ≤ x.1 → (rexp x = 0 ↔ x.2.IsUnitary) ∧ (x.2.IsUnitary ↔ (CG.mk x.2).IsUnitary) := by
  intro E _ _ _ x ha
  refine ⟨?_, (CG.isUnitary_mk _).symm⟩
  have hc : ∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ :=
    Classical.epsilon_spec (p := fun c : ℂ => ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ)
      (by rw [zc_eq_scL]; exact Central.lie_scalar x.2 (1 : Cinf E))
  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hpos : (0 : ℝ) < x.1 * Module.finrank ℚ E := by positivity
  have hz := (zc_comm_mem_eigen E x.1).2.2
  rw [rexp, div_eq_zero_iff, or_iff_left hpos.ne']
  constructor
  · intro h0
    have hne : (x.1 * (Module.finrank ℚ E : ℂ)) ≠ 0 := by exact_mod_cast hpos.ne'
    obtain ⟨χ, h1, -, h2, -⟩ := exists_abs_cpow E (-cex x / (x.1 * (Module.finrank ℚ E : ℂ)))
    have hre : (-cex x / (x.1 * (Module.finrank ℚ E : ℂ))).re = 0 := by
      rw [← Nat.cast_mul, Complex.div_natCast_re, Complex.neg_re, h0]; simp
    have hχ : χ.IsUnitary := fun y => by
      rw [h2, hre, nu, Model.eq_one_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E 0)]
      exact isUnitary_one y
    have hn : IsNormalised (x.2.twist χ) := by
      rintro _ ⟨φ, hφ, rfl⟩ t g
      have h3 : zc E x.1 (mulChi x.1 χ φ) = (0 : ℂ) • mulChi x.1 χ φ := by
        rw [h1, hc φ hφ, mul_div_cancel₀ _ hne, ← add_smul, add_neg_cancel, map_smul]
      simpa using (hz _ 0).1 h3 t g
    obtain ⟨ω, hω⟩ := Central.exists_hasCentral E x.1 x.2
    have h4 := ((hω.twist χ).isUnitary_iff.1 (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn)).mul
      (isUnitary_pow hχ x.1).inv
    rw [mul_inv_cancel_right] at h4
    exact hω.isUnitary_iff.2 h4
  · intro hu
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 x.2.ne_bot
    obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := Function.ne_iff.1 fun e => h0 (Subtype.ext e)
    have h1 := congrArg norm ((hz φ _).1 (hc φ hφ) 1 g)
    rw [splitCentre_eq_scalar, hu.norm_eq hφ, norm_mul, Complex.norm_exp] at h1
    have h2 := (mul_eq_right₀ (norm_ne_zero_iff.2 hg)).1 h1.symm
    simpa using h2

end GlobalTheory.ResW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivContinuousCharacterRealUnitaryOneParameter
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section
namespace GlobalTheory.HoweD
open scoped Matrix
open GlobalTheory.RealLift.OneParam GlobalTheory.RealLift.CharTrace

theorem prod_charD {ι : Type} [Fintype ι] [DecidableEq ι] {R S : ι → ℕ} (χ : (∀ w, Mat (R w) (S w)) → ℂ)
    (hmul : ∀ g h : ∀ w, Mat (R w) (S w), (∀ w, (g w)ᴴ * Jm (R w) (S w) * g w = Jm (R w) (S w)) → (∀ w, (h w)ᴴ * Jm (R w) (S w) * h w = Jm (R w) (S w)) →
      χ (g * h) = χ g * χ h)
    (hc : ContinuousOn χ {g | ∀ w, (g w)ᴴ * Jm (R w) (S w) * g w = Jm (R w) (S w)})
    (hne : ∀ g : ∀ w, Mat (R w) (S w), (∀ w, (g w)ᴴ * Jm (R w) (S w) * g w = Jm (R w) (S w)) → χ g ≠ 0) :
    ∃ n : ι → ℤ, ∀ g : ∀ w, Mat (R w) (S w), (∀ w, (g w)ᴴ * Jm (R w) (S w) * g w = Jm (R w) (S w)) → χ g = ∏ w, (g w).det ^ n w := by
  have upd : ∀ w (a : Mat (R w) (S w)), aᴴ * Jm (R w) (S w) * a = Jm (R w) (S w) → ∀ v,
      (Function.update (1 : ∀ w, Mat (R w) (S w)) w a v)ᴴ * Jm (R v) (S v) * Function.update (1 : ∀ w, Mat (R w) (S w)) w a v = Jm (R v) (S v) := by
    intro w a ha v
    by_cases hv : v = w
    · subst hv; simpa using ha
    · rw [Function.update_of_ne hv]; exact mem_one
  have key : ∀ w, ∃ n : ℤ, ∀ a : Mat (R w) (S w), aᴴ * Jm (R w) (S w) * a = Jm (R w) (S w) →
      χ (Function.update (1 : ∀ w, Mat (R w) (S w)) w a) = a.det ^ n := by
    intro w
    refine charUpq (R w) (S w) (fun a => χ (Function.update (1 : ∀ w, Mat (R w) (S w)) w a)) ?_ ?_ ?_
    · intro a b ha hb
      have e : Function.update (1 : ∀ w, Mat (R w) (S w)) w (a * b) =
          Function.update (1 : ∀ w, Mat (R w) (S w)) w a * Function.update (1 : ∀ w, Mat (R w) (S w)) w b := by
        funext v
        by_cases hv : v = w
        · subst hv; simp
        · simp [Function.update_of_ne hv]
      rw [e]
      exact hmul _ _ (upd w a ha) (upd w b hb)
    · exact hc.comp (show Continuous (Function.update (1 : ∀ w, Mat (R w) (S w)) w) from continuous_const.update w continuous_id).continuousOn
        fun a ha => upd w a ha
    · intro a ha; exact hne _ (upd w a ha)
  choose n hn using key
  refine ⟨n, fun g hg => ?_⟩
  have h1 : χ 1 = 1 := by
    have e := hmul 1 1 (fun _ => mem_one) (fun _ => mem_one)
    rw [mul_one] at e
    have hz := hne 1 (fun _ => mem_one)
    exact mul_left_cancel₀ hz (e.symm.trans (mul_one _).symm)
  have pc : ∀ (s : Finset ι) v, (s.piecewise g 1 v)ᴴ * Jm (R v) (S v) * s.piecewise g 1 v = Jm (R v) (S v) := by
    intro s v
    by_cases hv : v ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ hv]; exact hg v
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hv]; exact mem_one
  have ind : ∀ s : Finset ι, χ (s.piecewise g 1) = ∏ w ∈ s, (g w).det ^ n w := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert a s ha ih =>
      have e : (insert a s).piecewise g 1 = Function.update (1 : ∀ w, Mat (R w) (S w)) a (g a) * s.piecewise g 1 := by
        funext v
        by_cases hv : v = a
        · subst hv; simp [Finset.piecewise, ha]
        · simp [Finset.piecewise, hv, Function.update_of_ne hv]
      rw [e, hmul _ _ (upd a (g a) (hg a)) (pc s), hn a (g a) (hg a), ih, Finset.prod_insert ha]
  simpa using ind Finset.univ

theorem deriv_charD :
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ ν : UG (cA σ) J → ℂ,
      (∀ g h : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) →
      ContinuousOn ν {g : UG (cA σ) J | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} →
      (∀ g : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0) →
      ∃ k : InfinitePlace F → ℂ, ∀ γ ∈ RLines (σ := σ) J, ∀ Y, IsGenD τ C γ Y →
        HasDerivAt (fun t : ℝ => ν (γ (Multiplicative.ofAdd t))) (∑ w, k w * (Y w).trace) 0 := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hCM hC ν hmul hcont hne
  have := hCM.1
  obtain ⟨ξ, hξ⟩ := exists_moved hCM
  have hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0 := fun w => im_ne_zero hCM hξ (τ w).1
  choose C' hC' using fun w => (hC w).2
  have hL : ∀ w, C' w * C w = 1 := fun w => frame_inv (hC w).1 (hC' w)
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  set U : Set (∀ w : InfinitePlace F, Mat (R w) (S w)) := {h | ∀ w, (h w)ᴴ * Jm (R w) (S w) * h w = Jm (R w) (S w)} with hU
  set Λ : (∀ w : InfinitePlace F, Mat (R w) (S w)) → Matrix β β (AE F E) :=
    fun h => 1 + liftM τ ξ (fun w => C w * h w * C' w - 1) with hΛ
  have Λπ : ∀ h w, (Λ h).map (piInf (τ w)) = C w * h w * C' w := fun h w => by
    rw [hΛ, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), OneParam.liftM_map τ hξ', add_sub_cancel]
  have Λat : ∀ h, At (evI F) (Λ h - 1) := fun h => by
    rw [hΛ, add_sub_cancel_left]
    exact at_liftM τ ξ _
  have Λmul : ∀ h h', Λ (h * h') = Λ h * Λ h' := fun h h' => by
    refine (eq_of_at hCM τ ?_ fun w => ?_).symm
    · have e : Λ h * Λ h' - Λ (h * h') = (Λ h - 1) * Λ h' + (Λ h' - 1) - (Λ (h * h') - 1) := by noncomm_ring
      rw [e]
      exact at_sub (at_add (at_mul_right (Λat h) _) (Λat h')) (Λat _)
    · rw [Matrix.map_mul, Λπ, Λπ, Λπ, Pi.mul_apply]
      calc C w * h w * C' w * (C w * h' w * C' w) = C w * h w * (C' w * C w) * h' w * C' w := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have Λone : Λ 1 = 1 := eq_of_at hCM τ (Λat 1) fun w => by
    rw [Λπ, Pi.one_apply, Matrix.mul_one, hC' w, Matrix.map_one _ (map_zero _) (map_one _)]
  have ΛU : ∀ h ∈ U, (Λ h)ᵀ * J * (Λ h).map (cA σ) = J := fun h hh => by
    refine eq_of_at hCM τ ?_ fun w => ?_
    · have e : (Λ h)ᵀ * J * (Λ h).map (cA σ) - J =
          (Λ h - 1)ᵀ * J * (Λ h).map (cA σ) + J * (Λ h - 1).map (cA σ) := by
        have e1 : (Λ h - 1).map (cA σ) = (Λ h).map (cA σ) - 1 := by
          rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
        rw [e1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
          Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      exact at_add (at_mul_right (at_mul_right (at_transpose (Λat h)) _) _)
        (at_mul_left (at_map_cA σ (Λat h)) _)
    · have hc : ((Λ h).map (cA σ)).map (piInf (τ w)) = (C w * h w * C' w).map star := by
        rw [← Λπ h w, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map, Λπ]
      by_cases hb : b = 0
      · haveI := isEmpty_of_zero (hb ▸ (hC w).1) (hC' w)
        ext i
        exact isEmptyElim i
      · have h1 := conj_unit (hC w).1 (hC' w) ((form_iff (h w)).1 (hh w))
        rw [Matrix.mul_smul, Matrix.smul_mul] at h1
        exact smul_right_injective _ hb h1
  set hinv : (∀ w : InfinitePlace F, Mat (R w) (S w)) → ∀ w : InfinitePlace F, Mat (R w) (S w) :=
    fun h w => Jm (R w) (S w) * (h w)ᴴ * Jm (R w) (S w) with hhinv
  have inv_mul : ∀ h ∈ U, hinv h * h = 1 := fun h hh => by
    funext w
    rw [Pi.mul_apply, hhinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Jm (R w) (S w)) (h w), hh w,
      jm_mul_self, Pi.one_apply]
  have mul_inv : ∀ h ∈ U, h * hinv h = 1 := fun h hh => by
    funext w
    have := congrFun (inv_mul h hh) w
    rw [Pi.mul_apply, Pi.one_apply] at this ⊢
    exact mul_eq_one_comm.1 this
  have Λinv1 : ∀ h ∈ U, Λ h * Λ (hinv h) = 1 := fun h hh => by rw [← Λmul, mul_inv h hh, Λone]
  have Λinv2 : ∀ h ∈ U, Λ (hinv h) * Λ h = 1 := fun h hh => by rw [← Λmul, inv_mul h hh, Λone]
  let G : U → UG (cA σ) J := fun h => ⟨⟨Λ h, Λ (hinv h), Λinv1 h h.2, Λinv2 h h.2⟩, ΛU h h.2⟩
  have LevelValuationRings : ∀ h, At (evI F) (((G h).1 : Matrix β β (AE F E)) - 1) := fun h => Λat h
  have Gmul : ∀ h h' : U, ∀ hm : (h : ∀ w : InfinitePlace F, Mat (R w) (S w)) * h' ∈ U, G ⟨_, hm⟩ = G h * G h' :=
    fun h h' hm => Subtype.ext (Units.ext (Λmul h h'))
  have Λc : Continuous Λ := continuous_const.add ((continuous_liftM τ ξ).comp (continuous_pi fun w =>
    (((continuous_const.matrix_mul (continuous_apply w)).matrix_mul continuous_const).sub continuous_const)))
  have hinvc : Continuous hinv := continuous_pi fun w =>
    (continuous_const.matrix_mul (continuous_apply w).matrix_conjTranspose).matrix_mul continuous_const
  have Gc : Continuous G := by
    have hu : Continuous fun h : U => ((G h).1 : GL β (AE F E)) :=
      Units.continuous_iff.2 ⟨Λc.comp continuous_subtype_val, (Λc.comp hinvc).comp continuous_subtype_val⟩
    exact hu.subtype_mk _
  classical
  let χ : (∀ w : InfinitePlace F, Mat (R w) (S w)) → ℂ := fun h => if hh : h ∈ U then ν (G ⟨h, hh⟩) else 0
  have χG : ∀ h : U, χ h = ν (G h) := fun h => by simp only [χ, dif_pos h.2]
  have memU : ∀ h h' : ∀ w : InfinitePlace F, Mat (R w) (S w), h ∈ U → h' ∈ U → h * h' ∈ U := fun h h' hh hh' w =>
    mem_mul (hh w) (hh' w)
  obtain ⟨n, hn⟩ := prod_charD (R := R) (S := S) χ
    (fun g h hg hh => by
      rw [χG ⟨g, hg⟩, χG ⟨h, hh⟩, χG ⟨g * h, memU g h hg hh⟩, Gmul ⟨g, hg⟩ ⟨h, hh⟩]
      exact hmul _ _ (LevelValuationRings _) (LevelValuationRings _))
    (by
      rw [continuousOn_iff_continuous_restrict]
      convert hcont.comp_continuous Gc LevelValuationRings using 1
      funext h
      exact χG h)
    (fun g hg => by rw [χG ⟨g, hg⟩]; exact hne _ (LevelValuationRings _))
  refine ⟨fun w => (n w : ℂ), fun γ hγ Y hY => ?_⟩
  set e : ℝ → ∀ w : InfinitePlace F, Mat (R w) (S w) := fun t w => NormedSpace.exp (t • Y w) with he
  have hγw : ∀ t w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = C w * e t w * C' w :=
    fun t w => by
      rw [he]; simp only
      rw [← hY t w, Matrix.mul_assoc, hC' w, Matrix.mul_one]
      rfl
  have heU : ∀ t, e t ∈ U := fun t w => by
    rw [form_iff]
    set g := ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) with hg
    have hgU : gᵀ * (b • J.map (piInf (τ w))) * g.map star = b • J.map (piInf (τ w)) := by
      have hu : ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E))ᵀ * J *
          ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (cA σ) = J := (γ (Multiplicative.ofAdd t)).2
      have := congrArg (fun X => X.map (piInf (τ w))) hu
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      have hc : (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (cA σ)).map (piInf (τ w)) = g.map star := by
        rw [hg, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [hc] at this
      rw [Matrix.mul_smul, Matrix.smul_mul, this]
    have hee : e t w = C' w * g * C w := by
      rw [hg, hγw, Matrix.mul_assoc, Matrix.mul_assoc, hL, Matrix.mul_one, ← Matrix.mul_assoc, hL, Matrix.one_mul]
    have t1 : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC' w, Matrix.transpose_one]
    have t2 : (C w).map star * (C' w).map star = 1 := by
      rw [← map_star_mul, hC' w]; exact Matrix.map_one _ (star_zero _) (star_one _)
    rw [hee, ← (hC w).1]
    calc (C' w * g * C w)ᵀ * ((C w)ᵀ * (b • J.map (piInf (τ w))) * (C w).map star) * (C' w * g * C w).map star
        = (C w)ᵀ * (gᵀ * (((C' w)ᵀ * (C w)ᵀ) * (b • J.map (piInf (τ w))) * ((C w).map star * (C' w).map star)) *
            g.map star) * (C w).map star := by
          rw [map_star_mul, map_star_mul, Matrix.transpose_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = (C w)ᵀ * (b • J.map (piInf (τ w))) * (C w).map star := by
          rw [t1, t2, Matrix.one_mul, Matrix.mul_one, hgU]
  have hγe : ∀ t, γ (Multiplicative.ofAdd t) = G ⟨e t, heU t⟩ := fun t => by
    refine Subtype.ext (Units.ext (eq_of_at hCM τ ?_ fun w => ?_))
    · have e1 : ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - Λ (e t) =
          (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1) - (Λ (e t) - 1) := by abel
      show At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - Λ (e t))
      rw [e1]
      exact at_sub (hγ.2 _) (Λat _)
    · show ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = (Λ (e t)).map (piInf (τ w))
      rw [hγw, Λπ]
  have hval : ∀ t : ℝ, ν (γ (Multiplicative.ofAdd t)) =
      Complex.exp ((t : ℂ) * ∑ w, (n w : ℂ) * (Y w).trace) := fun t => by
    rw [hγe t, ← χG, hn _ (heU t), Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [he]; simp only
    rw [GlobalTheory.DetSqrtCover.det_exp, ← Complex.exp_int_mul, Matrix.trace_smul]
    congr 1
    simp only [Complex.real_smul]
    ring
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ∑ w, (n w : ℂ) * (Y w).trace))
      (∑ w, (n w : ℂ) * (Y w).trace) 0 := by
    have h0 := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (∑ w, (n w : ℂ) * (Y w).trace)).cexp
    simpa using h0
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hval)

end GlobalTheory.HoweD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockSymbolMatrixNeZero
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem det_blockSymbolMatrix_ne_zero (E : Type) [Field E] (J : Type) [Fintype J] [DecidableEq J]
    (δ e : ℕ) (g : Fin δ → E) (R : Matrix (Fin δ) (Fin δ) E) (hg : ∀ p, g p ≠ 0) (hR : R.det ≠ 0) :
    (Matrix.of fun i i' : J × Fin δ => if i.1 = i'.1 then g i.2 ^ e * R i.2 i'.2 else 0).det ≠ 0 := by
  set A : Matrix (J × Fin δ) (J × Fin δ) E :=
    Matrix.of fun i i' : J × Fin δ => if i.1 = i'.1 then g i.2 ^ e * R i.2 i'.2 else 0 with hA
  have key : Matrix.reindex (Equiv.prodComm J (Fin δ)) (Equiv.prodComm J (Fin δ)) A =
      Matrix.blockDiagonal (fun _ : J => Matrix.diagonal (fun p => g p ^ e) * R) := by
    ext ⟨p, j⟩ ⟨p', j'⟩
    simp [A, Matrix.blockDiagonal_apply, Matrix.diagonal_mul]
  rw [← Matrix.det_reindex_self (Equiv.prodComm J (Fin δ)) A, key, Matrix.det_blockDiagonal]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  rw [Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ (hg p)) hR

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetIsMultiHomogeneous
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.DetHom

section MH

variable {R : Type} [CommSemiring R] {B n : ℕ}

theorem mh_zero (a : Fin B → ℕ) : IsMultiHomogeneous a (0 : MvPolynomial (Fin B × Fin n) R) := by
  intro s hs; simp at hs

theorem mh_C (r : R) : IsMultiHomogeneous (0 : Fin B → ℕ) (C r : MvPolynomial (Fin B × Fin n) R) := by
  classical
  intro s hs b
  rw [mem_support_iff, coeff_C] at hs
  have : (0 : Fin B × Fin n →₀ ℕ) = s := by
    by_contra h; exact hs (if_neg h)
  subst this; simp

theorem mh_X (i : Fin B) (j : Fin n) :
    IsMultiHomogeneous (Pi.single i 1) (X (i, j) : MvPolynomial (Fin B × Fin n) R) := by
  classical
  intro s hs b
  rw [mem_support_iff, coeff_X'] at hs
  have : Finsupp.single (i, j) 1 = s := by
    by_contra h; exact hs (if_neg h)
  subst this
  by_cases hb : b = i
  · subst hb; simp [Finsupp.single_apply]
  · simp [Finsupp.single_apply, hb, Pi.single_apply]

theorem mh_add {a : Fin B → ℕ} {f g : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (hg : IsMultiHomogeneous a g) : IsMultiHomogeneous a (f + g) := by
  classical
  intro s hs
  rcases Finset.mem_union.1 (support_add hs) with h | h
  exacts [hf s h, hg s h]

theorem mh_sum {ι : Type} (t : Finset ι) {a : Fin B → ℕ} (f : ι → MvPolynomial (Fin B × Fin n) R)
    (hf : ∀ i ∈ t, IsMultiHomogeneous a (f i)) : IsMultiHomogeneous a (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using mh_zero (R := R) (n := n) a
  | insert x t hx ih =>
    rw [Finset.sum_insert hx]
    exact mh_add (hf x (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem mh_smul {S : Type} [SMulZeroClass S R] {a : Fin B → ℕ} (c : S) {f : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) : IsMultiHomogeneous a (c • f) :=
  fun s hs => hf s (support_smul hs)

theorem mh_mul {a b : Fin B → ℕ} {f g : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (hg : IsMultiHomogeneous b g) : IsMultiHomogeneous (a + b) (f * g) := by
  classical
  intro s hs i
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.1 (support_mul f g hs)
  simp [Finset.sum_add_distrib, hf u hu i, hg v hv i]

theorem mh_prod {ι : Type} (t : Finset ι) (a : ι → Fin B → ℕ) (f : ι → MvPolynomial (Fin B × Fin n) R)
    (hf : ∀ i ∈ t, IsMultiHomogeneous (a i) (f i)) : IsMultiHomogeneous (∑ i ∈ t, a i) (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using mh_C (R := R) (B := B) (n := n) 1
  | insert x t hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    exact mh_mul (hf x (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end MH

def cnt {B t : ℕ} (β : Fin t → Fin B) (b : Fin B) : ℕ := (Finset.univ.filter fun q => β q = b).card

theorem sum_cnt {B t : ℕ} (β : Fin t → Fin B) : ∑ b, cnt β b = t := by
  classical
  unfold cnt
  rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (β x))]
  simp

theorem sum_single_eq_cnt {B t : ℕ} (β : Fin t → Fin B) :
    (∑ i, (Pi.single (β i) 1 : Fin B → ℕ)) = cnt β := by
  classical
  funext b
  simp only [Finset.sum_apply, Pi.single_apply, cnt]
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : β i = b
  · simp [h]
  · simp [h, Ne.symm h]

theorem mh_coordP {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N B t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (c : A →ₗ[K] K) (β : Fin t → Fin B) (m : A) :
    IsMultiHomogeneous (cnt β) (coordP mul c β m) := by
  classical
  unfold coordP
  refine mh_sum _ _ fun e _ => ?_
  have h := mh_mul (mh_C (R := K) (B := B) (n := N) (c (word mul (fun i => Pi.single (e i) 1) m)))
    (mh_prod Finset.univ (fun i => (Pi.single (β i) 1 : Fin B → ℕ)) (fun i => (X (β i, e i) : MvPolynomial (Fin B × Fin N) K))
      fun i _ => mh_X (β i) (e i))
  rwa [zero_add, sum_single_eq_cnt] at h

end GlobalTheory.HSShort.DetHom


open GlobalTheory.HSShort.DetHom in
theorem GlobalTheory.HSShort.det_isMultiHomogeneous : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A) (d : ℕ) (c : Fin d → A →ₗ[F] F) (col : Fin d → S.Col), ∃ a : Fin (S.D + 1) → ℕ, IsMultiHomogeneous a (S.det c col) ∧ ∑ i, a i = ∑ k, (col k).t := by
  intro F A _ _ _ _ _ _ S d c col
  classical
  refine ⟨∑ k, cnt (col k).β, ?_, ?_⟩
  · unfold Sys.det
    rw [Matrix.det_apply]
    refine mh_sum _ _ fun σ _ => mh_smul _ ?_
    have h := mh_prod Finset.univ (fun k => cnt (col k).β)
      (fun k => (Matrix.of fun i k => coordP S.mul (c i) (col k).β ((col k).x : A)) (σ k) k)
      fun k _ => by simpa using mh_coordP S.mul (c (σ k)) (col k).β ((col k).x : A)
    exact h
  · simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => sum_cnt (col k).β
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionNonemptyNonvanishingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisation_section_nonempty_nonvanishing : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), IsIntegral (Over.mk t ⊗ P.A).left → ∃ θ : LB.Sec (LB.LinComb P.L (K := Fin 1) ![(snd (Over.mk t) P.A).left] ![1]), (nonzeroLocus θ : Set (Over.mk t ⊗ P.A).left).Nonempty := by
  first | exact @GlobalTheory.FibreTheta.exists_sec_nonempty | exact GlobalTheory.FibreTheta.exists_sec_nonempty | (intros; apply GlobalTheory.FibreTheta.exists_sec_nonempty <;> assumption)
end

