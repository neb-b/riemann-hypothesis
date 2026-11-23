module

public import Mathlib
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftSmoothingProdExpSmoothCommute
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.LeftSmoothing

open scoped Manifold Topology
open Set Filter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem contMDiff_prodExp (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) :
    letI := h.chartedSpace; ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, 𝔤) ∞ (h.prodExp X) := by
  letI := h.chartedSpace
  intro t
  refine h.contMDiffAt_of_val ?_
  have e : (fun s => (((h.prodExp X s : G) : 𝔸ˣ) : 𝔸)) = prodExpVal (fun i => (X i : 𝔸)) :=
    funext fun s => h.val_prodExp X s
  rw [e]
  exact (contDiff_prodExpVal _).contMDiff.contMDiffAt

theorem contDiff_param (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) {f : G → ℂ}
    (hf : h.IsSmoothFun f) (g : G) :
    ContDiff ℝ ∞ (fun p : 𝔤 × (Fin n → ℝ) => f (h.prodExp X p.2 * g * h.expG p.1)) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, 𝔤 × (Fin n → ℝ)) 𝓘(ℝ, 𝔤) ∞
      (fun p : 𝔤 × (Fin n → ℝ) => h.prodExp X p.2 * g * h.expG p.1) :=
    (((contMDiff_prodExp h X).comp contDiff_snd.contMDiff).mul contMDiff_const).mul
      (h.contMDiff_expG_comp contDiff_fst)
  exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf hm).contDiff

theorem continuous_iteratedFDeriv_partial {P T E' : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {Φ : P × T → E'} (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) :
    Continuous (fun p : P × T => iteratedFDeriv ℝ k (fun Y => Φ (Y, p.2)) p.1) := by
  set L := ContinuousLinearMap.inl ℝ P T
  set H : P × T → ContinuousMultilinearMap ℝ (fun _ : Fin k => P) E' :=
    fun q => ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L) (iteratedFDeriv ℝ k Φ q)
  have hH : Continuous H :=
    (ContinuousLinearMap.continuous _).comp (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hpart : ∀ (Z : T) (Y : P), iteratedFDeriv ℝ k (fun Y => Φ (Y, Z)) Y = H (Y, Z) := by
    intro Z Y
    have e : (fun Y => Φ (Y, Z)) = (fun w => Φ (w + (0, Z))) ∘ L := by
      funext Y; simp [L]
    have hΦZ : ContDiff ℝ ∞ (fun w : P × T => Φ (w + (0, Z))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [e, L.iteratedFDeriv_comp_right hΦZ Y (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    simp [H, L]
  have e : (fun p : P × T => iteratedFDeriv ℝ k (fun Y => Φ (Y, p.2)) p.1) = H := by
    funext p; exact hpart p.2 p.1
  rw [e]; exact hH

variable (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ)

noncomputable def integrand (f : G → ℂ) (g : G) (Y : 𝔤) (t : Fin n → ℝ) : ℂ :=
  κ t * f (h.prodExp X t * g * h.expG Y)

noncomputable def conv (f : G → ℂ) (y : G) : ℂ :=
  ∫ t, κ t * f (h.prodExp X t * y)

theorem conv_mul_expG (f : G → ℂ) (g : G) (Y : 𝔤) :
    conv h X κ f (g * h.expG Y) = ∫ t, integrand h X κ f g Y t := by
  simp only [conv, integrand, mul_assoc]

variable {h X κ}

theorem contDiff_slice {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (t : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) :=
  (contDiff_param h X hf g).comp (contDiff_id.prodMk contDiff_const)

theorem iter_integrand_eq {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (k : ℕ) (Y : 𝔤)
    (t : Fin n → ℝ) :
    ParamIntegral.iter (integrand h X κ f g) k Y t =
      (ContinuousLinearMap.mul ℝ ℂ (κ t)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) Y) := by
  rw [ParamIntegral.iter]
  have e : (fun Y => integrand h X κ f g Y t) =
      (ContinuousLinearMap.mul ℝ ℂ (κ t)) ∘ (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) := by
    funext Y; simp [integrand]
  rw [e]
  exact (ContinuousLinearMap.mul ℝ ℂ (κ t)).iteratedFDeriv_comp_left
    (contDiff_slice hf g t).contDiffAt (by exact_mod_cast le_top)

theorem integrand_contDiff {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (t : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun Y => integrand h X κ f g Y t) := by
  have e : (fun Y => integrand h X κ f g Y t) =
      (ContinuousLinearMap.mul ℝ ℂ (κ t)) ∘ (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) := by
    funext Y; simp [integrand]
  rw [e]
  exact (ContinuousLinearMap.mul ℝ ℂ (κ t)).contDiff.comp (contDiff_slice hf g t)

theorem integrand_cont (hκ : Continuous κ) {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (k : ℕ) :
    Continuous (fun p : 𝔤 × (Fin n → ℝ) => ParamIntegral.iter (integrand h X κ f g) k p.1 p.2) := by
  simp_rw [iter_integrand_eq hf]
  have hc := continuous_iteratedFDeriv_partial (contDiff_param h X hf g) k
  have hL : Continuous (fun t => ContinuousLinearMap.mul ℝ ℂ (κ t)) :=
    (ContinuousLinearMap.mul ℝ ℂ).continuous.comp hκ
  have hB := ContinuousLinearMap.continuous₂ (𝕜 := ℝ) (E := ℂ →L[ℝ] ℂ)
    (F := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) ℂ)
    (G := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) ℂ)
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => 𝔤) ℂ ℂ)
  exact hB.comp ((hL.comp continuous_snd).prodMk hc)

theorem integrand_supp (hκs : HasCompactSupport κ) (f : G → ℂ) (g : G) (Y₀ : 𝔤) :
    ∃ U ∈ 𝓝 Y₀, ∃ C : Set (Fin n → ℝ), IsCompact C ∧
      ∀ Y ∈ U, ∀ t ∉ C, integrand h X κ f g Y t = 0 :=
  ⟨univ, univ_mem, tsupport κ, hκs, fun Y _ t ht => by
    simp [integrand, image_eq_zero_of_notMem_tsupport ht]⟩

theorem isSmoothFun_conv (hκ : Continuous κ) (hκs : HasCompactSupport κ) {f : G → ℂ}
    (hf : h.IsSmoothFun f) : h.IsSmoothFun (conv h X κ f) := by
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g
  simp_rw [conv_mul_expG]
  exact contDiff_integral_of_iteratedFDeriv _ (integrand_contDiff hf g)
    (integrand_cont hκ hf g) (integrand_supp hκs f g)

theorem rightDeriv_conv (hκ : Continuous κ) (hκs : HasCompactSupport κ) {f : G → ℂ}
    (hf : h.IsSmoothFun f) (Z : 𝔤) (g : G) :
    h.rightDeriv Z (conv h X κ f) g = conv h X κ (h.rightDeriv Z f) g := by
  show fderiv ℝ (fun Y : 𝔤 => conv h X κ f (g * h.expG Y)) 0 Z = _
  simp_rw [conv_mul_expG]
  rw [← iteratedFDeriv_one_apply (fun _ : Fin 1 => Z),
    iteratedFDeriv_integral_eq _ (integrand_contDiff hf g) (integrand_cont hκ hf g)
      (integrand_supp hκs f g) 1]
  have hint : Integrable (fun t => ParamIntegral.iter (integrand h X κ f g) 1 (0 : 𝔤) t) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((integrand_cont hκ hf g 1).comp (continuous_const.prodMk continuous_id)) ?_
    refine HasCompactSupport.intro hκs fun t ht => ParamIntegral.iter_eq_zero_of_eventually ?_
    exact Eventually.of_forall fun Y => by
      simp [integrand, image_eq_zero_of_notMem_tsupport ht]
  rw [ContinuousMultilinearMap.integral_apply hint]
  simp only [conv]
  congr 1
  funext t
  rw [iter_integrand_eq hf]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.mul_apply']
  rw [iteratedFDeriv_one_apply]
  rfl


variable (h X) in
noncomputable def convEnd (hκ : Continuous κ) (hκs : HasCompactSupport κ) :
    Module.End ℂ (h.smoothFuns (F := ℂ)) where
  toFun f := ⟨conv h X κ f, isSmoothFun_conv hκ hκs f.2⟩
  map_add' f₁ f₂ := by
    apply Subtype.ext
    funext y
    have hc : ∀ f : h.smoothFuns (F := ℂ), Integrable (fun t => κ t * (f : G → ℂ) (h.prodExp X t * y)) := by
      intro f
      have hfc : Continuous (f : G → ℂ) := by
        letI := h.chartedSpace
        exact (show h.IsSmoothFun (f : G → ℂ) from f.2).continuous
      exact (hκ.mul (hfc.comp ((h.continuous_prodExp X).mul continuous_const))).integrable_of_hasCompactSupport
        (hκs.mul_right)
    show ∫ t, κ t * ((f₁ : G → ℂ) + f₂) (h.prodExp X t * y) = (∫ t, κ t * (f₁ : G → ℂ) (h.prodExp X t * y)) + ∫ t, κ t * (f₂ : G → ℂ) (h.prodExp X t * y)
    rw [← integral_add (hc f₁) (hc f₂)]
    congr 1; funext t; simp [mul_add]
  map_smul' c f := by
    apply Subtype.ext
    funext y
    show ∫ t, κ t * (c • (f : G → ℂ)) (h.prodExp X t * y) = c * ∫ t, κ t * (f : G → ℂ) (h.prodExp X t * y)
    rw [← integral_const_mul]
    congr 1; funext t; simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem commute_convEnd (hκ : Continuous κ) (hκs : HasCompactSupport κ) (Z : 𝔤) :
    h.rightDerivEnd (F := ℂ) Z * convEnd h X hκ hκs = convEnd h X hκ hκs * h.rightDerivEnd Z := by
  refine LinearMap.ext fun f => Subtype.ext (funext fun y => ?_)
  exact rightDeriv_conv hκ hκs f.2 Z y

theorem adjoin_commute_convEnd (hκ : Continuous κ) (hκs : HasCompactSupport κ)
    {T : Module.End ℂ (h.smoothFuns (F := ℂ))}
    (hT : T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ)))) :
    T * convEnd h X hκ hκs = convEnd h X hκ hκs * T := by
  have hle : Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) ≤
      Subalgebra.centralizer ℂ {convEnd h X hκ hκs} := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨Z, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro A hA
    rw [Set.mem_singleton_iff] at hA
    subst hA
    exact (commute_convEnd hκ hκs Z).symm
  have := (Subalgebra.mem_centralizer_iff ℂ).1 (hle hT) _ rfl
  exact this.symm

end GlobalTheory.LeftSmoothing


open GlobalTheory.LeftSmoothing in
theorem GlobalTheory.leftSmoothing_prodExp :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (n : ℕ) (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ), Continuous κ → HasCompactSupport κ → ∀ f : h.smoothFuns (F := ℂ), ∃ v : h.smoothFuns (F := ℂ), (∀ y, (v : G → ℂ) y = ∫ t, κ t * (f : G → ℂ) (h.prodExp X t * y)) ∧ ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y, (T v : G → ℂ) y = ∫ t, κ t * (T f : G → ℂ) (h.prodExp X t * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h n X κ hκ hκs f
  refine ⟨convEnd h X hκ hκs f, fun y => rfl, fun T hT y => ?_⟩
  have e := LinearMap.congr_fun (adjoin_commute_convEnd (X := X) hκ hκs hT) f
  simp only [Module.End.mul_apply] at e
  rw [e]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem TateIsoO.ev_nsmul {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIsoO D k Q act e) (n m : ℕ) (x : D.La) :
    I.ev n (m • x) = I.ev n x ^ m := by
  let f : D.La →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (I.ev n x)) fun x y => by
    simp [I.add]
  exact congrArg Additive.toMul (map_nsmul f m x)

theorem levelPos_of_coprime {N' : ℕ} (hc : N'.Coprime p) : 0 < N' := by
  rcases Nat.eq_zero_or_pos N' with h | h
  · subst h
    exact absurd ((Nat.coprime_zero_left p).1 hc) (Fact.out : p.Prime).one_lt.ne'
  · exact h

def Obj.forget {b : Base D R} {N' : ℕ} {s : S ⟶ Sp R} (o : Obj b N' s) (N : ℕ) (hd : N ∣ N')
    (hc : N'.Coprime p) : Obj b N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := o.kerP
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta y := o.eta ((N' / N) • y)
  eta_add x y := by rw [smul_add, o.eta_add]
  eta_lin c x := by rw [smul_comm, o.eta_lin]
  eta_ker x := by rw [smul_smul, Nat.div_mul_cancel hd, o.eta_ker]
  geom k _ _ x β h := by
    obtain ⟨I, hI⟩ := o.geom k x β h
    have hN' := levelPos_of_coprime hc
    have hN : 0 < N := Nat.pos_of_dvd_of_pos hd hN'
    have hk : 0 < N' / N := Nat.div_pos (Nat.le_of_dvd hN' hd) hN
    refine ⟨I, fun y => ?_⟩
    rw [hI, I.ev_nsmul]
    have := I.tower N (N' / N) hN hk (by rw [Nat.mul_div_cancel' hd]; exact hc) y
    rwa [Nat.mul_div_cancel' hd] at this

@[simp] theorem Obj.forget_eta {b : Base D R} {N' : ℕ} {s : S ⟶ Sp R} (o : Obj b N' s) (N : ℕ) (hd : N ∣ N')
    (hc : N'.Coprime p) (y : D.La) : (o.forget N hd hc).eta y = o.eta ((N' / N) • y) := rfl

def IsLift {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) (T : Over S)
    (lv : D.La → (T ⟶ o.A)) : Prop :=
  (∀ x y, lv (x + y) = lv x * lv y) ∧
  (∀ x, lv (N' • x) = 1) ∧
  (∀ (c : D.O) x, lv (c • x) = lv x ≫ o.act.act c) ∧
  (∀ x, lv ((N' / N) • x) = toUnit T ≫ o.eta x) ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
    ∃ I : TateIsoO D k (Over.mk (x ≫ T.hom) ⟶ o.A) (fun c g => g ≫ o.act.act c)
        (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
      ∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv y = I.ev N' y

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqSiegelParabolicOperatorEq
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem parFun_lintegral_sq : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ : Matrix α ν E → ℂ, ∫⁻ x, ‖parFun c ψ χ Q (mat c p) φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q _ ψ _ hψ1 _ χ _ hres _ _ μ _ p hp φ
  obtain ⟨h1, -, -⟩ := _root_.GlobalTheory.KSp.sieg_blocks F E c δ hE ν p hp
  obtain ⟨-, htop, -, -, -, -, -, -⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  obtain ⟨-, -, -, hnorm, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  have h1' := mul_eq_one_comm.mp h1
  let A : GL ν E := ⟨(mat c p).toBlocks₁₁, _, h1, h1'⟩
  have hA : ((A : GL ν E) : Matrix ν ν E) = (mat c p).toBlocks₁₁ := rfl
  set D : NNReal := distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det A)) with hD
  have hD0 : D ≠ 0 := distribHaarChar_pos.ne'
  have hsc : ‖sc F χ (Fintype.card α) (mat c p).toBlocks₁₁.det‖ₑ ^ 2 = ((D ^ Fintype.card α : NNReal) : ENNReal) := by
    have := hnorm (Matrix.GeneralLinearGroup.det A)
    have hd : ((Matrix.GeneralLinearGroup.det A : Eˣ) : E) = (mat c p).toBlocks₁₁.det := rfl
    rw [hd] at this
    rw [enorm_eq_nnnorm, ← ENNReal.coe_pow]
    congr 1
    apply NNReal.eq
    push_cast
    rw [this]
    rfl
  have hpt : ∀ x, ‖parFun c ψ χ Q (mat c p) φ x‖ₑ ^ 2 =
      ((D ^ Fintype.card α : NNReal) : ENNReal) * ‖φ (x * (A : Matrix ν ν E))‖ₑ ^ 2 := by
    intro x
    have hψe : ∀ t, ‖ψ t‖ₑ = 1 := fun t => by
      rw [enorm_eq_nnnorm]; simp [← NNReal.coe_eq_one, coe_nnnorm, hψ1 t]
    simp only [parFun, enorm_mul, hψe, one_mul, mul_pow, hsc, hA]
  haveI := htop
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun x => x * (A : Matrix ν ν E)
      invFun := fun x => x * ((A⁻¹ : GL ν E) : Matrix ν ν E)
      left_inv := fun x => by simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      right_inv := fun x => by simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      continuous_toFun := Continuous.matrix_mul continuous_id continuous_const
      continuous_invFun := Continuous.matrix_mul continuous_id continuous_const }
  have hmap : μ.map (e.toMeasurableEquiv) = ((D ^ Fintype.card α)⁻¹ : NNReal) • μ := by
    have := _root_.GlobalTheory.KSp.map_twoSided_haar F E c δ hE α ν μ 1 A
    have hf : (fun x : Matrix α ν E => ((1 : GL α E) : Matrix α α E) * x * (A : Matrix ν ν E)) = e.toMeasurableEquiv := by
      funext x; simp [e]
    rw [hf] at this
    rw [this, ← hD]
    simp
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  have hl := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) e.toMeasurableEquiv (μ := μ)
  have hl' : ∫⁻ x, ‖φ (x * (A : Matrix ν ν E))‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂(μ.map e.toMeasurableEquiv) := hl.symm
  rw [hl', hmap, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul,
    mul_inv_cancel₀ (pow_ne_zero _ hD0), ENNReal.coe_one, one_mul]

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAtPrimeEtaleCompat
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_at_prime_etale_compat : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA)
      (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) := by
  first | (exact @GlobalTheory.KeyOriginBC.pointAtZero_bc) | (exact GlobalTheory.KeyOriginBC.pointAtZero_bc) | (intros; apply GlobalTheory.KeyOriginBC.pointAtZero_bc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFlatEtaleSheafLocallyDivisibleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyFlatEtaleSheaf_locally_divisible : ∀ (Q q e : ℕ) [NeZero Q], q * e = Q → ∀ (M : Shv (ZMod Q)), FlatS M → ∀ (U : Scheme.{0}) (x : Sec M U), e • x = 0 → Loc U fun V g => ∃ y : Sec M V, Sec.res g x = q • y := by
  first | (exact @GlobalTheory.EtC.FlatLoc.flat_loc) | (exact GlobalTheory.EtC.FlatLoc.flat_loc) | (intros; apply GlobalTheory.EtC.FlatLoc.flat_loc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeIsKInjectiveBijectiveHypercohomologyI
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.EtC.cone_kinj_and_bijective_iff : ∀ (R : Type) [CommRing R] {D C : Cx R} (f : D ⟶ C) (m : ℤ),
    D.IsStrictlyGE m → C.IsStrictlyGE m → (∀ n, CategoryTheory.Injective (D.X n)) →
    (∀ n, CategoryTheory.Injective (C.X n)) → (mappingCone f).IsKInjective ∧ ∀ K : Cx R,
      ((∀ n, Function.Bijective (cpush K f n)) ↔ ∀ n, Subsingleton (CohomologyClass K (mappingCone f) n)) := by
  intro R _ D C f m hD hC iD iC
  refine ⟨?_, ?_⟩
  · haveI : ∀ n, Injective ((mappingCone f).X n) := fun n =>
      Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl).symm
        (@Injective.instBiprod _ _ _ _ _ _ (iD (n + 1)) (iC n))
    haveI : (mappingCone f).IsStrictlyGE (m - 1) := CochainComplex.isStrictlyGE_mappingCone f m m (m - 1) (by omega)
    exact isKInjective_of_injective _ (m - 1)
  · intro K
    have ex := fun n => GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K f n
    constructor
    · intro hb n
      refine ⟨fun x y => ?_⟩
      have h0 : ∀ x : CohomologyClass K (mappingCone f) n, x = 0 := by
        intro x
        have h1 : cpush K f (n + 1) (cpost K (mappingCone.fst f) n (n + 1) rfl x) = 0 :=
          ((ex n).2.2 _).2 ⟨x, rfl⟩
        have h2 : cpost K (mappingCone.fst f) n (n + 1) rfl x = 0 :=
          (hb (n + 1)).1 (by rw [h1, map_zero])
        obtain ⟨y, rfl⟩ := ((ex n).2.1 x).1 h2
        obtain ⟨z, rfl⟩ := (hb n).2 y
        exact ((ex n).1 _).2 ⟨z, rfl⟩
      rw [h0 x, h0 y]
    · intro hs n
      refine ⟨?_, fun y => ?_⟩
      · rw [injective_iff_map_eq_zero]
        intro z hz
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by ring⟩
        obtain ⟨w, rfl⟩ := ((ex k).2.2 z).1 hz
        rw [Subsingleton.elim w 0, map_zero]
      · exact ((ex n).1 y).1 (Subsingleton.elim _ _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOnePrimeIntegralClosureIffDvdIrreduciblStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_heightOne_prime_integralClosure_iff_dvd_irreducible : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (Q : Ideal B), Q.IsPrime → Q.height = 1 → ∀ (t : A), Irreducible t → (∀ b : B, (b : K) = algebraMap F K t → b ∈ Q) → ∀ (a : A) (b : B), (b : K) = algebraMap F K a → (b ∈ Q ↔ t ∣ a) := by
  first | (exact @GlobalTheory.JacVal.mem_iff_dvd_of_height_one) | (exact GlobalTheory.JacVal.mem_iff_dvd_of_height_one) | (intros; apply GlobalTheory.JacVal.mem_iff_dvd_of_height_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfForallHeightOneLocalizationIntegrallyClosedStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_forall_heightOne_localization_integrallyClosed : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (z : K), (∀ Q : Ideal A, Q.IsPrime → Q.height = 1 → ∃ r c : A, r ∉ Q ∧ algebraMap A K r * z = algebraMap A K c) → ∃ c : A, z = algebraMap A K c := by
  first | (exact @GlobalTheory.NormalHeightOne.mem_of_forall_height_eq_one) | (exact GlobalTheory.NormalHeightOne.mem_of_forall_height_eq_one) | (intros; apply GlobalTheory.NormalHeightOne.mem_of_forall_height_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStandardOpenCoordinateRingIffLocalizationCharStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ y : F, y ∈ rA k x I ↔ ∃ N : ℕ, y * (∏ j ∈ I, x j / x i) ^ N ∈ rA k x {i} := by
  first | (exact @GlobalTheory.PD.rA_eq_loc) | (exact GlobalTheory.PD.rA_eq_loc) | (intros; apply GlobalTheory.PD.rA_eq_loc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosuStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure : ∀ (D : Type) [CommRing D] [IsDomain D], AIC (integralClosure D (AlgebraicClosure (FractionRing D))) := by
  first | (exact @GlobalTheory.aic_integralClosure_algebraicClosure) | (exact GlobalTheory.aic_integralClosure_algebraicClosure) | (intros; apply GlobalTheory.aic_integralClosure_algebraicClosure  <;> assumption)
end

