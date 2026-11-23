module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHeckeMellinGaussIntegrandEqProdGamma
section
open NumberField MeasureTheory

noncomputable section
namespace GlobalTheory.HeckeMellinProd

theorem hmon_real_mul (n : ℤ) (c : ℝ) (z : ℂ) :
    GlobalTheory.HeckeTheta.hmon n ((c : ℂ) * z) = (c : ℂ) ^ n.natAbs * GlobalTheory.HeckeTheta.hmon n z := by
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · rw [map_mul, Complex.conj_ofReal, mul_pow]; congr 2; omega
  · rw [mul_pow]; congr 2; omega

def fac (w : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))

theorem coord (n : ℤ) (s : ℂ) (v : ℂ) (y : ℝ) :
    GlobalTheory.HeckeTheta.hmon n ((Real.exp (y / 2) : ℂ) * v) *
      Complex.exp ((-2 * Real.pi * ‖(Real.exp (y / 2) : ℂ) * v‖ ^ 2 : ℝ) : ℂ) * Complex.exp (s * (y : ℂ)) =
    GlobalTheory.HeckeTheta.hmon n v * fac (s + ((|n| : ℤ) : ℂ) / 2) (‖v‖ ^ 2) y := by
  rw [hmon_real_mul, fac]
  have h1 : ((Real.exp (y / 2) : ℝ) : ℂ) ^ n.natAbs = Complex.exp ((n.natAbs : ℂ) * (y / 2)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]; push_cast; rfl
  have h2 : ‖(Real.exp (y / 2) : ℂ) * v‖ ^ 2 = Real.exp y * ‖v‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
      ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have h3 : ((|n| : ℤ) : ℂ) = (n.natAbs : ℂ) := by
    rw [← Int.natCast_natAbs, Int.cast_natCast]
  rw [h1, h2, h3]
  have e1 : ((-2 * Real.pi * (Real.exp y * ‖v‖ ^ 2) : ℝ) : ℂ) = -(((2 * Real.pi * ‖v‖ ^ 2 * Real.exp y) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e1]
  calc _ = GlobalTheory.HeckeTheta.hmon n v * (Complex.exp ((n.natAbs : ℂ) * (y / 2)) * Complex.exp (s * (y : ℂ))) *
        Complex.exp (-(((2 * Real.pi * ‖v‖ ^ 2 * Real.exp y) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [← Complex.exp_add, mul_assoc]; congr 3; ring

theorem term_eq (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ) (v : I → ℂ) (y : I → ℝ) :
    GlobalTheory.HeckeMellin.term n s v y =
      ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * fac (s + ((|n i| : ℤ) : ℂ) / 2) (‖v i‖ ^ 2) (y i) := by
  unfold GlobalTheory.HeckeMellin.term GlobalTheory.HeckeTheta.gauss GlobalTheory.HeckeTheta.dil
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact coord (n i) s (v i) (y i)

theorem norm_fac (w : ℂ) (r : ℝ) (t : ℝ) :
    ‖fac w r t‖ = Real.exp (w.re * t) * Real.exp (-(2 * Real.pi * r * Real.exp t)) := by
  rw [fac, norm_mul, Complex.norm_exp, Complex.norm_exp]
  congr 2
  · simp

theorem ofReal_norm_fac (w : ℂ) (r : ℝ) (t : ℝ) :
    ((‖fac w r t‖ : ℝ) : ℂ) = fac (w.re : ℂ) r t := by
  rw [norm_fac, fac]; push_cast; rfl

end GlobalTheory.HeckeMellinProd

namespace GlobalTheory.HeckeMellinProd

theorem fac_int (w : ℂ) (hw : 0 < w.re) (r : ℝ) (hr : 0 < r) :
    Integrable (fac w r) ∧ ∫ t, fac w r t = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) :=
  _root_.GlobalTheory.HeckeMellin.gamma_integral_exp_substitution r hr w hw

theorem norm_fac_int (w : ℂ) (hw : 0 < w.re) (r : ℝ) (hr : 0 < r) :
    ∫ t, ‖fac w r t‖ = Real.Gamma w.re * (2 * Real.pi * r) ^ (-w.re) := by
  have h := (fac_int (w.re : ℂ) (by simpa using hw) r hr).2
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [ofReal_norm_fac]
  rw [h, Complex.ofReal_mul (Real.Gamma w.re), Complex.ofReal_cpow (by positivity), ← Complex.Gamma_ofReal]
  push_cast; ring_nf

theorem mellin_prod : ∀ (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ v : I → ℂ, (∀ i, v i ≠ 0) → Integrable (GlobalTheory.HeckeMellin.term n s v) ∧ ∫ y, GlobalTheory.HeckeMellin.term n s v y = ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) * ((2 * Real.pi * ‖v i‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s v y‖ = ∏ i, ‖v i‖ ^ (n i).natAbs * Real.Gamma (s.re + (|n i| : ℝ) / 2) * (2 * Real.pi * ‖v i‖ ^ 2) ^ (-(s.re + (|n i| : ℝ) / 2)) := by
  intro I _ n s hs v hv
  have hw : ∀ i, 0 < (s + ((|n i| : ℤ) : ℂ) / 2).re := fun i => by
    have : (0 : ℝ) ≤ |((n i : ℤ) : ℝ)| := abs_nonneg _
    simp only [Complex.add_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
    norm_num
    positivity
  have hr : ∀ i, 0 < ‖v i‖ ^ 2 := fun i => pow_pos (norm_pos_iff.2 (hv i)) 2
  have hwre : ∀ i, (s + ((|n i| : ℤ) : ℂ) / 2).re = s.re + (|n i| : ℝ) / 2 := fun i => by
    simp [Complex.add_re, Complex.div_re]
  set g : I → ℝ → ℂ := fun i t => GlobalTheory.HeckeTheta.hmon (n i) (v i) * fac (s + ((|n i| : ℤ) : ℂ) / 2) (‖v i‖ ^ 2) t with hg
  have hterm : GlobalTheory.HeckeMellin.term n s v = fun y => ∏ i, g i (y i) := funext (term_eq I n s v)
  have hgi : ∀ i, Integrable (g i) := fun i => ((fac_int _ (hw i) _ (hr i)).1.const_mul _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hterm]; exact Integrable.fintype_prod (μ := fun _ => volume) hgi
  · rw [hterm, integral_fintype_prod_volume_eq_prod g]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hg]
    rw [integral_const_mul, (fac_int _ (hw i) _ (hr i)).2]; ring
  · have hn : (fun y => ‖GlobalTheory.HeckeMellin.term n s v y‖) = fun y => ∏ i, (fun i t => ‖g i t‖) i (y i) := by
      rw [hterm]; funext y; exact norm_prod _ _
    rw [hn, integral_fintype_prod_volume_eq_prod (fun i t => ‖g i t‖)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hg, norm_mul]
    rw [integral_const_mul, norm_fac_int _ (hw i) _ (hr i), GlobalTheory.HeckeTheta.norm_hmon, hwre]; ring

end GlobalTheory.HeckeMellinProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvPullbackPgl
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem pull_htCast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn; subst hi; rfl

theorem pull_cpow (q : ℕ) [NeZero q] (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x : Ht q E 2 1) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_htCast, (hA q).2.1 f hE']
  | succ k ih => rw [cpow_succ, cpow_succ, pull_htCast, (hA q).1, ih]

theorem inv_pullback_pgl (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) :
    Inv q (pullback V (PGL.pr N)) := fun U ⟨x⟩ => hE U ⟨Sx.map (pullback.fst V (PGL.pr N)) x⟩

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartSelfStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInCharacterIsotypicPart_self : ∀ (G : Type) [Group G] [Finite G] (Y : G → ℂ), IsChar ℂ ℂ Y → Kills Y Y := by
  first | (exact @GlobalTheory.Shin.kills_self) | (exact GlobalTheory.Shin.kills_self) | (intros; apply GlobalTheory.Shin.kills_self  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTateTwistResolutionTensorFlat
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section
variable {R : Type} [CommRing R]

theorem sec_map_res' {F G : Shv R} (ψ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U) :
    Sec.map ψ (Sec.res g z) = Sec.res g (Sec.map ψ z) :=
  congrArg (fun f => f.hom z) (ψ.hom.naturality g.op)

theorem sec_map_comp' {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sec_map_id' {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem flatS_of_iso {M N : Shv R} (i : M ≅ N) (h : FlatS M) : FlatS N := by
  obtain ⟨P, φ, hs, hi, hf⟩ := h
  refine ⟨P, φ ≫ i.hom.hom, ?_, ?_, hf⟩
  · intro U y
    obtain ⟨S, hS, hP⟩ := hs U (Sec.map i.inv y)
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    refine ⟨x, ?_⟩
    change Sec.map i.hom ((φ.app (op V)).hom x) = Sec.res g y
    rw [hx, sec_map_res', ← sec_map_comp', i.inv_hom_id, sec_map_id']
  · intro U x hx
    refine hi U x ?_
    have h1 : Sec.map i.inv (Sec.map i.hom ((φ.app (op U)).hom x)) = Sec.map i.inv (0 : Sec N U) :=
      congrArg (Sec.map i.inv) hx
    rw [← sec_map_comp', i.hom_inv_id, sec_map_id'] at h1
    exact h1.trans (map_zero _)

theorem flatS_of_isZero {M : Shv R} (h : IsZero M) : FlatS M := by
  have hsub : ∀ U : Scheme.{0}, Subsingleton (Sec M U) := fun U => by
    have h1 : IsZero M.obj := (sheafToPresheaf _ _).map_isZero h
    exact ModuleCat.subsingleton_of_isZero (((evaluation _ _).obj (op U)).map_isZero h1)
  refine ⟨M.obj, 𝟙 _, fun U y => ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => ⟨Sec.res g y, rfl⟩⟩,
    fun U x _ => ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => (hsub V).elim _ _⟩, fun U _ => ?_⟩
  haveI := hsub U
  change Module.Flat _ (Sec M U)
  infer_instance

theorem flatS_sgl {F : Shv R} (h : FlatS F) (t : ℤ) : FlatS ((sgl F).X t) := by
  by_cases ht : t = 0
  · subst ht
    exact flatS_of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm h
  · exact flatS_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht)

end

theorem isTwRes_tensor : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor → IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ) := by
  intro q _ i j k hk I J T e e' hI hJ hflat τ hτ
  obtain ⟨hIge, εI, hεI, heI⟩ := hI
  obtain ⟨hJge, εJ, hεJ, heJ⟩ := hJ
  obtain ⟨μ, hμ, hμgen⟩ := GlobalTheory.T.tateTwist_mul_isTensorPairing q i j k hk
  obtain ⟨T₁, τ₁, hτ₁⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (sgl (tw q i)) J
  have hTge : T.IsStrictlyGE 0 := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ).2.1 hIge hJge
  obtain ⟨u₁, hu₁, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) μ hμ).1 τ₁ (𝟙 _) εJ
  obtain ⟨u₂, hu₂, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ₁ hτ₁).1 τ εI (𝟙 J)
  obtain ⟨ν, hμν, -, hνt⟩ := GlobalTheory.T.exists_isFlip_sheafComplexPairing (ZMod q) μ
  obtain ⟨ν₁, hν₁, -, hν₁t⟩ := GlobalTheory.T.exists_isFlip_sheafComplexPairing (ZMod q) τ₁
  have hflati : ∀ t, FlatS ((sgl (tw q i)).X t) := flatS_sgl (flatS_tw q i)
  have hid : ∀ {K : Cx (ZMod q)} (t : ℤ) {U : Scheme.{0}} (x : Sec (K.X t) U), Sec.map (HomologicalComplex.Hom.f (𝟙 K) t) x = x :=
    fun _ _ _ => rfl
  haveI := hIge
  haveI := hJge
  haveI := hεI
  haveI := hεJ
  have hc : ν.Compat ν₁ εJ (𝟙 _) u₁ := by
    intro U s t w h a b
    rw [hμν U t s w (by omega) b a, hid, hν₁ U t s w (by omega) b (Sec.map (εJ.f s) a), Units.smul_def,
      Units.smul_def]
    have h1 := hu₁ U t s w (by omega) b a
    rw [hid] at h1
    rw [← h1]
    exact map_zsmul ((u₁.f w).hom.app (op U)).hom _ _
  have hq1 : QuasiIso u₁ := GlobalTheory.T.tensor_flat_complex_preserves_quasiIso (ZMod q) ν ν₁ (hνt hμ) (hν₁t hτ₁) hflati εJ u₁ hc
  have hq2 : QuasiIso u₂ := GlobalTheory.T.tensor_flat_complex_preserves_quasiIso (ZMod q) τ₁ τ hτ₁ hτ hflat εI u₂ hu₂
  refine ⟨hTge, u₁ ≫ u₂, quasiIso_comp (hφ := hq1) (hφ' := hq2) _ _, fun U ζ => ?_⟩
  rw [← hμgen U ζ]
  change Sec.map (u₂.f 0) (Sec.map (u₁.f 0) _) = _
  rw [hu₁ U 0 0 0 (add_zero 0), hu₂ U 0 0 0 (add_zero 0), hid, hid, heI, heJ]

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrictionStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefect_restriction : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → Sec.res g (GlobalTheory.EtC.RedChern.defect Q q U v) = GlobalTheory.EtC.RedChern.defect Q q V (Units.map g.appTop.hom.toMonoidHom v) := by
  first
  | exact @GlobalTheory.EtC.RedChern.res_defect
  | exact GlobalTheory.EtC.RedChern.res_defect
  | (intros; apply GlobalTheory.EtC.RedChern.res_defect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplacePolynomialKernelDerivativeWordsFamily
section
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

theorem solGFam_foldr_rightDeriv_leftTranslate (l : List 𝔤) (f : G → ℂ) (x : G) :
    l.foldr h.rightDeriv (fun y => f (x * y)) = fun y => l.foldr h.rightDeriv f (x * y) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    funext g
    simp only [List.foldr_cons, ih]
    simp only [IsExpLieAlgebra.rightDeriv, mul_assoc]

theorem solGFam_isSmoothFun_foldr_rightDeriv (l : List 𝔤) {f : G → ℂ} (hf : h.IsSmoothFun f) :
    h.IsSmoothFun (l.foldr h.rightDeriv f) := by
  induction l with
  | nil => exact hf
  | cons X l ih => exact h.isSmoothFun_rightDeriv ih X

theorem solGFam_foldr_rightDeriv_smul_add (l : List 𝔤) {f f' : G → ℂ} (hf : h.IsSmoothFun f)
    (hf' : h.IsSmoothFun f') (c : ℂ) :
    l.foldr h.rightDeriv (c • f + f') = c • l.foldr h.rightDeriv f + l.foldr h.rightDeriv f' := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [List.foldr_cons, ih]
    have h1 := GlobalTheory.HCA.solGFam_isSmoothFun_foldr_rightDeriv h l hf
    have h2 := GlobalTheory.HCA.solGFam_isSmoothFun_foldr_rightDeriv h l hf'
    have h3 : h.IsSmoothFun (c • l.foldr h.rightDeriv f) := (h.smoothFuns (F := ℂ)).smul_mem c h1
    rw [h.rightDeriv_add h3 h2, h.rightDeriv_smul h1]

end GlobalTheory.HCA

theorem GlobalTheory.HCA.solG_smFn : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → (∀ f ∈ solG h b P, Continuous f) ∧ (∀ f ∈ solG h b P, ∀ g, (fun y => f (g * y)) ∈ solG h b P) ∧ ∃ K : Set G, IsCompact K ∧ ∀ l₀ : List 𝔤, SmFn h b μ (solG h b P) K fun l f => (l.map b ++ l₀).foldr h.rightDeriv f 1 := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP _ _ μ hμ
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨hs, -⟩ := (mem_solG h b).1 hf
    letI := h.chartedSpace
    exact ContMDiff.continuous hs
  · intro f hf g
    obtain ⟨hs, h0⟩ := (mem_solG h b).1 hf
    obtain ⟨f', hf'1, hf'2⟩ := GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps 𝔸 G 𝔤 h ⟨f, hs⟩ g
    have hΔ : (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ∈
        Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _
        (Algebra.subset_adjoin ⟨b i, rfl⟩) (Algebra.subset_adjoin ⟨b i, rfl⟩)
    have hT : Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P ∈
        Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hΔ) (Polynomial.aeval_mem_adjoin_singleton ℂ _)
    have e : (f' : G → ℂ) = fun y => f (g * y) := funext hf'1
    rw [mem_solG]
    refine ⟨e ▸ f'.2, ?_⟩
    have hf'eq : (⟨fun y => f (g * y), e ▸ f'.2⟩ : h.smoothFuns (F := ℂ)) = f' := Subtype.ext e.symm
    rw [hf'eq]
    ext y
    rw [hf'2 _ hT y, h0]
    rfl
  · obtain ⟨K, hK, hC⟩ := GlobalTheory.T.exists_compact_derivWord_bound_of_aeval_casimir 𝔸 G 𝔤 h d b P hP μ hμ
    refine ⟨K, hK, fun l₀ => ⟨?_, ?_, ?_⟩⟩
    · intro l f hf f' hf' c
      obtain ⟨hs, -⟩ := (mem_solG h b).1 hf
      obtain ⟨hs', -⟩ := (mem_solG h b).1 hf'
      simp only [GlobalTheory.HCA.solGFam_foldr_rightDeriv_smul_add h _ hs hs' c, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · intro l
      obtain ⟨C, hC'⟩ := hC (l.map b ++ l₀)
      refine ⟨C, fun f hf => ?_⟩
      obtain ⟨hs, h0⟩ := (mem_solG h b).1 hf
      exact hC' ⟨f, hs⟩ h0
    · intro l i f hf
      obtain ⟨hs, -⟩ := (mem_solG h b).1 hf
      have hL := GlobalTheory.HCA.solGFam_isSmoothFun_foldr_rightDeriv h (l.map b ++ l₀) hs
      have hd := h.hasDerivAt_rightDeriv hL (b i) 1
      simp only [List.map_cons, List.cons_append, List.foldr_cons]
      refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [GlobalTheory.HCA.solGFam_foldr_rightDeriv_leftTranslate h, mul_one, one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationPullbackInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_pullback_injective : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∀ (n i : ℤ) (x : Ht q (sp (Localization.Away f)) n i) (y : Ht q (sp A') n i), pull _ (spMap (Localization.awayMap (algebraMap A A') f)) _ _ x = pull _ (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) _ _ y → ∃ b : Ht q (sp A) n i, pull _ (spMap (algebraMap A (Localization.Away f))) _ _ b = x ∧ pull _ (spMap (algebraMap A A')) _ _ b = y := by
  first | (exact @GlobalTheory.EtC.MVEtale.mv_etale_mid) | (exact GlobalTheory.EtC.MVEtale.mv_etale_mid) | (intros; apply GlobalTheory.EtC.MVEtale.mv_etale_mid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapInfSupPowEq
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem map_comap_inf_sup_pow_eq : ∀ (W W' : Scheme.{0}) [IsAffine W] [IsLocallyNoetherian W] (π : W' ⟶ W)
    (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (K τ : W.IdealSheafData),
    (∀ x, x ∉ K.support → x ∈ U) →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (τ.comap π).map π ⊓ (τ ⊔ K ^ k) = τ := by
  intro W W' _ _ π U hqc hiso K τ hK
  let T : W.affineOpens := ⟨⊤, isAffineOpen_top W⟩
  haveI : IsNoetherianRing Γ(W, T.1) := IsLocallyNoetherian.component_noetherian T
  have hle : τ ≤ (τ.comap π).map π := Scheme.IdealSheafData.le_map_comap τ π
  have htor : ∀ b ∈ ((τ.comap π).map π).ideal T, ∀ f ∈ K.ideal T, ∃ m : ℕ, f ^ m * b ∈ τ.ideal T := by
    intro b hb f hf
    have hV : (W.affineBasicOpen f).1 ≤ U := by
      intro x hx
      by_contra hxU
      have hxK : x ∈ K.support := by_contra fun h => hxU (hK x h)
      rw [Scheme.IdealSheafData.mem_support_iff] at hxK
      exact (Scheme.mem_zeroLocus_iff W _ x).1 (hxK T) f hf hx
    have heq := _root_.GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict W W' π U hqc hiso τ (W.affineBasicOpen f) hV
    rw [← Scheme.IdealSheafData.map_ideal_basicOpen, ← Scheme.IdealSheafData.map_ideal_basicOpen] at heq
    have hloc := T.2.isLocalization_basicOpen f
    have hb' := Ideal.mem_map_of_mem (W.presheaf.map (homOfLE (W.basicOpen_le f)).op).hom hb
    rw [heq] at hb'
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) Γ(W, W.basicOpen f)
        (τ.ideal T) b).1 hb'
    exact ⟨m, hm⟩
  obtain ⟨k₀, hk₀⟩ := _root_.GlobalTheory.inf_sup_pow_eq_of_torsion Γ(W, T.1) (K.ideal T) (τ.ideal T) (((τ.comap π).map π).ideal T)
    (hle T) htor
  refine ⟨k₀, fun k hk => Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  exact hk₀ k hk

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisExactEtaleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mayer_vietoris_exact_etale : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ n i : ℤ, ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A'' : Type) [CommRing A''] [Algebra A A''] [Algebra.Etale A A''] (φ : A' →ₐ[A] A''), IsNbhd A A'' f → ∀ z, pull _ (spMap (awayHom φ f)) _ _ z = 0 → δ z = 0 := by
  first | (exact @GlobalTheory.EtC.ExcisionNat.excision_natural) | (exact GlobalTheory.EtC.ExcisionNat.excision_natural) | (intros; apply GlobalTheory.EtC.ExcisionNat.excision_natural <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageConnectedComponentRationalPointFieldExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem preimage_connectedComponent_rationalPoint_baseChange : ∀ (k k' : Type) [Field k] [Field k'] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k')) (p : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) (q : X' ⟶ X) (e : Spec (CommRingCat.of k) ⟶ X) (e' : Spec (CommRingCat.of k') ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' connectedComponent (e (IsLocalRing.closedPoint k)) = connectedComponent (e' (IsLocalRing.closedPoint k')) := by
  intro k k' _ _ X X' f f' p q e e' hf hP he he' hq
  have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set x : X := e (IsLocalRing.closedPoint k) with hx
  set x' : X' := e' (IsLocalRing.closedPoint k') with hx'
  have hopen : IsOpen (connectedComponent x) := _root_.GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian X hN x
  let U : X.Opens := ⟨connectedComponent x, hopen⟩
  have hsub : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hrange : Set.range e ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim y (IsLocalRing.closedPoint k)]
    exact mem_connectedComponent
  let eU : Spec (CommRingCat.of k) ⟶ U.toScheme := IsOpenImmersion.lift U.ι e hrange
  have heU : eU ≫ U.ι = e := IsOpenImmersion.lift_fac _ _ _
  have hUc : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := x))
  have hgc : GeometricallyConnected (U.ι ≫ f) :=
    _root_.GlobalTheory.geometricallyConnected_of_smooth_of_section k U.toScheme (U.ι ≫ f) eU inferInstance (by rw [← Category.assoc, heU, he]) hUc
  have hP1 : IsPullback (q ∣_ U) (q ⁻¹ᵁ U).ι U.ι q := isPullback_morphismRestrict q U
  have hP2 : IsPullback (q ∣_ U) ((q ⁻¹ᵁ U).ι ≫ f') (U.ι ≫ f) p := hP1.paste_vert hP
  have hc : ConnectedSpace (q ⁻¹ᵁ U).toScheme :=
    GeometricallyConnected.geometrically_connectedSpace (f := U.ι ≫ f) p _ _ hP2
  have hc' : _root_.IsConnected (q ⁻¹' connectedComponent x) :=
    isConnected_iff_connectedSpace.mpr hc
  have hmem : x' ∈ q ⁻¹' connectedComponent x := by
    have : q x' = x := by
      have h1 : q x' = (e' ≫ q) (IsLocalRing.closedPoint k') := rfl
      have h2 : (p ≫ e) (IsLocalRing.closedPoint k') = e (p (IsLocalRing.closedPoint k')) := rfl
      rw [h1, hq, h2]
      exact congrArg e (Subsingleton.elim _ _)
    rw [Set.mem_preimage, this]
    exact mem_connectedComponent
  have hclopen : IsClopen (q ⁻¹' connectedComponent x) :=
    IsClopen.preimage ⟨isClosed_connectedComponent, hopen⟩ q.continuous
  exact Set.Subset.antisymm (hc'.subset_connectedComponent hmem)
    (hclopen.connectedComponent_subset hmem)

end GlobalTheory
end

