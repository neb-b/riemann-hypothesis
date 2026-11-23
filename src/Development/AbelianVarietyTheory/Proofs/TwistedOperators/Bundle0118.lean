module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevChiFlagLEqOne
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem norm_residueChar_eq_one {E : Type} [Field E] [NumberField E] (PP : Pl E) (f : (kP PP)ˣ →* ℂˣ) (x : (kP PP)ˣ) :
    ‖((f x : ℂˣ) : ℂ)‖ = 1 := by

  have hx : IsOfFinOrder x := isOfFinOrder_of_finite x
  have hpow : ((f x : ℂˣ) : ℂ) ^ orderOf x = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow hx.orderOf_pos.ne'

theorem norm_levChi_flagL_eq_one :
    ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank),
      ∀ κ ∈ levG V β (flagL L), ‖levChi V β (flagL L) κ‖ = 1 := by
  intro D V β L κ _

  have hP : ∀ x, ext1 (flagL L).P.H (flagL L).P.chi x = 1 := by
    intro x
    unfold ext1
    split_ifs
    · rfl
    · rfl

  rw [levChi, levFn, hP, one_mul, Units.val_mul, norm_mul, Units.coe_prod, Units.coe_prod, norm_prod,
    norm_prod, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP _
    exact norm_residueChar_eq_one PP _ _
  · intro PP _
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun c _ => norm_residueChar_eq_one PP _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeHtE
section
noncomputable section

namespace GlobalTheory.RatCount

open NumberField GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped TensorProduct
open scoped NNReal

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]


open Classical in
def htE (x : E) : ℝ≥0 :=
  (∏ w : InfinitePlace F, max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊)) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 (absFin F v ((1 : Fv F v) ⊗ₜ[F] x))

end GlobalTheory.RatCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitCharExp

theorem exists_zpow_of_trivial (ψ : ℂˣ →* Circle) (hc : Continuous ψ)
    (h : ∀ s : ℂˣ, starRingEnd ℂ (s : ℂ) = s → ψ (s * s) = 1) :
    ∃ k : ℤ, ∀ z : ℂˣ, ((ψ z : Circle) : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ k := by
  have hu : Continuous (Circle.toUnits : Circle →* ℂˣ) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    exact (continuous_subtype_val.comp (continuous_inv (G := Circle))).congr fun u => by simp [Function.comp, Circle.coe_inv]
  obtain ⟨k, hk⟩ := GlobalTheory.circle_hom_eq_zpow (ψ.comp Circle.toUnits) (hc.comp hu)
  refine ⟨k, fun z => ?_⟩
  have h0 : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.ne_zero
  have h1 : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have hs : ((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 h0).ne'
  let u : Circle := ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
    simp [Submonoid.unitSphere, h0.ne']⟩
  have hu' : (u : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := rfl
  have e : z = Circle.toUnits u * (Units.mk0 _ hs * Units.mk0 _ hs) := by
    apply Units.ext
    show (z : ℂ) = (u : ℂ) * (((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ) * ((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ))
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0.le, hu', div_mul_cancel₀ _ h1]
  have e2 : ψ z = u ^ k := by
    rw [e, map_mul, h _ (Complex.conj_ofReal _), mul_one]
    exact hk u
  rw [e2, ← hu', Circle.coe_zpow]

variable {D : D7} {θ : InfFam D}

theorem ext_of_chart {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) {a b : AE D}
    (h1 : finPart D a = finPart D b) (h2 : ∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) : a = b := by
  rw [← sub_eq_zero]
  refine h.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => ?_
  rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]

theorem exists_real_hom {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) :
    ∃ e : (D.what₂.Tau → ℂ) →* AE D, Continuous e ∧ (∀ z, finPart D (e z) = 1) ∧
      ∀ z τ, θ τ (infPart D (e z)) = z τ := by
  have a1 : ∀ z, finPart D (1 + σ (z - 1)) = 1 := fun z => by rw [RingHom.map_add (f := _), h.fin, add_zero, RingHom.map_one]
  have a2 : ∀ z τ, θ τ (infPart D (1 + σ (z - 1))) = z τ := fun z τ => by
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), h.comp, RingHom.map_one, RingHom.map_one]; simp
  refine ⟨{ toFun := fun z => 1 + σ (z - 1)
            map_one' := by rw [sub_self, σ.map_zero, add_zero]
            map_mul' := fun z w => ext_of_chart h (by rw [RingHom.map_mul, a1, a1, a1, mul_one]) fun τ => by
              rw [RingHom.map_mul, RingHom.map_mul, a2, a2, a2, Pi.mul_apply] }, ?_, a1, a2⟩
  exact continuous_const.add (h.cont.comp (continuous_id.sub continuous_const))

theorem map_sq_eq_one {χ : (AE D)ˣ →* Circle} {n : ℕ} (hχ : ResEta D χ n) (y : (AE D)ˣ)
    (hy : cA D (y : AE D) = y) : χ (y * y) = 1 := by
  obtain ⟨⟨η, hη⟩, h⟩ := hχ
  obtain ⟨-, -, hN, -⟩ := GlobalTheory.VolHeckeCompare.exists_form D
  have e : idF D (GlobalTheory.VolHeckeCompare.normU D y) = y * y := by
    refine (hN y).trans (Units.ext ?_)
    show (y : AE D) * cA D (y : AE D) = (y : AE D) * y
    rw [hy]
  rw [← e, h η hη, hη.2.2.1 y, one_pow]

theorem exists_hasInfExp : ∀ (D : D7) (θ : InfFam D) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau),
    IsInfFam θ → IsHeckeChar D χ → ResEta D χ n → ∃ a : ℚ, HasInfExp D χ τ a := by
  intro D θ χ n τ hθ hχ hr
  classical
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, ec, e1, e2⟩ := exists_real_hom h
  let f : ℂ →* AE D := e.comp (MonoidHom.mulSingle (fun _ : D.what₂.Tau => ℂ) τ)
  have fc : Continuous f := ec.comp (continuous_mulSingle (A := fun _ : D.what₂.Tau => ℂ) τ)
  have f1 : ∀ z, finPart D (f z) = 1 := fun z => e1 _
  have f2 : ∀ z τ', θ τ' (infPart D (f z)) = (Pi.mulSingle τ z : D.what₂.Tau → ℂ) τ' := fun z τ' => e2 _ τ'
  obtain ⟨k, hk⟩ := exists_zpow_of_trivial (χ.comp (Units.map f)) (hχ.1.comp (fc.units_map f)) fun s hs => by
    rw [MonoidHom.comp_apply, MonoidHom.map_mul]
    refine map_sq_eq_one hr _ (ext_of_chart h ?_ fun τ' => ?_)
    · have e3 : finPart D (cA D (f s)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (f s)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (f s)
      show finPart D (cA D (f s)) = finPart D (f s)
      rw [e3, f1, RingHom.map_one]
    · show θ τ' (infPart D (cA D (f s))) = θ τ' (infPart D (f s))
      rw [GlobalTheory.FockCompare.comp_cA hθ, f2]
      by_cases ht : τ' = τ
      · rw [ht, Pi.mulSingle_eq_same, hs]
      · rw [Pi.mulSingle_eq_of_ne ht, RingHom.map_one]
  refine ⟨(k : ℚ) / 2, k, by ring, ⟨θ, hθ⟩, fun θ' hθ' x x1 x2 => ?_⟩
  obtain rfl := GlobalTheory.VolHeckeCompare.infFam_unique hθ hθ'
  let z : ℂˣ := Units.map ((θ τ).comp (infPart D)).toMonoidHom x
  have hz : (z : ℂ) = θ τ (infPart D (x : AE D)) := rfl
  have ex : Units.map f z = x := by
    refine Units.ext (ext_of_chart h ((f1 z).trans x1.symm) fun τ' => (f2 z τ').trans ?_)
    by_cases ht : τ' = τ
    · rw [ht, Pi.mulSingle_eq_same, hz]
    · rw [Pi.mulSingle_eq_of_ne ht, x2 τ' ht]
  have := hk z
  rwa [MonoidHom.comp_apply, ex, hz] at this

end GlobalTheory.SplitCharExp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKOContinuousAndRatInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem thetaKO_continuous_and_rat_invariant : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → Continuous (fun p : GA D S × GA D T => thetaKO om p.1 p.2 f) ∧ ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ g h, thetaKO om (γ * g) (γ' * h) f = thetaKO om g h f := by
  intro D ψ S T χS χT om H f hf
  refine ⟨H.om_cont f hf 0, ?_⟩
  intro γ hγ γ' hγ' g h
  have h1 : om (γ * g, γ' * h) = om (γ, γ') * om (g, h) := by
    rw [← map_mul]; rfl
  unfold thetaKO
  rw [h1]
  exact H.om_aut γ hγ γ' hγ' _ (H.om_pres (g, h) f hf)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKORatLeftAndEigenRight
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem thetaKO_rat_left_and_eigen_right : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ g h, thetaKO om (γ * g) (γ' * h) f = thetaKO om g h f) ∧ ∀ k k' (c : ℂ), om (k, k') f = c • f → ∀ g h, thetaKO om (g * k) (h * k') f = c * thetaKO om g h f := by
  intro D ψ S T χS χT om hω f hf
  refine ⟨fun γ hγ γ' hγ' g h => ?_, fun k k' c hc g h => ?_⟩
  ·

    have hprod : ((γ * g, γ' * h) : GA D S × GA D T) = (γ, γ') * (g, h) := rfl
    unfold thetaKO
    rw [hprod, map_mul, Module.End.mul_apply]
    exact hω.om_aut γ hγ γ' hγ' _ (hω.om_pres (g, h) f hf)
  ·
    have hprod : ((g * k, h * k') : GA D S × GA D T) = (g, h) * (k, k') := rfl
    unfold thetaKO
    rw [hprod, map_mul, Module.End.mul_apply, hc, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftTranslateOfKernelFixed
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open NumberField IsDedekindDomain MeasureTheory in
open scoped TensorProduct InnerProductSpace in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.thetaLift_translate_of_kernel_fixed : ∀ {G H S Sinf Ds Dt : Type} [Group G] [Group H]
    [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds]
    [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (pt : Sinf → S)
    (It : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (io : CCs →ₗ[ℂ] CCt),
    _root_.Formalism.IndefR.Lift.IsIo ν 𝓕 th pt It CCs CCt io →
    (∀ u : CCt, (∀ φ v, (u : Dt →ₗ[ℂ] (G → ℂ)) (It φ v) = 0) → u = 0) →
    ∀ (k : G) (k' : H) (a a' : ℂ), (∀ g h φ, a * th (g * k) (h * k') (pt φ) = a' * th g h (pt φ)) →
    (∀ (F : CCs) φ v g, ∫ h in 𝓕, th g (h * k') (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k') ∂ν =
      ∫ h in 𝓕, th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h ∂ν) →
    ∀ (F F' : CCs) (u : CCt), (∀ v h, (F' : Ds →ₗ[ℂ] (H → ℂ)) v h = a' * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k')) →
    (∀ v g, (u : Dt →ₗ[ℂ] (G → ℂ)) v g = a * ((io F : CCt) : Dt →ₗ[ℂ] (G → ℂ)) v (g * k)) →
    io F' = u := by
  intro G H S Sinf Ds Dt _ _ _ _ _ _ _ _ _ ν 𝓕 th pt It CCs CCt io hio hker k k' a a' hth hinv
    F F' u hF' hu
  refine sub_eq_zero.mp (hker (io F' - u) fun φ v => ?_)
  funext g
  simp only [Submodule.coe_sub, LinearMap.sub_apply, Pi.sub_apply, Pi.zero_apply]
  rw [sub_eq_zero, ← hio.eq F' φ v g, hu, ← hio.eq F φ v (g * k)]
  unfold _root_.Formalism.IndefR.Lift.liftInt
  rw [← hinv F φ v (g * k), ← integral_const_mul]
  congr 1
  funext h
  rw [hF', show a * (th (g * k) (h * k') (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k')) =
    (a * th (g * k) (h * k') (pt φ)) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k') from
    (_root_.mul_assoc _ _ _).symm, hth]
  ring

end GlobalTheory
end

