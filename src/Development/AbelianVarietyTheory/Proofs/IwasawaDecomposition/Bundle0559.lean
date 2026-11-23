module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0546
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotPoleOfBounded
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcReg

theorem valR_eq_ev {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = ev x U h f := by
  rw [valR, dite_eq_left h]; rfl

theorem not_pole_of_bounded : ∀ (X : Scheme.{0}) (U₀ W₀ : X.Opens) (f₀ : Γ(X, W₀)) (χ : Sp (PowerSeries ℂ) ⟶ X) (y : ℂ → (Sp ℂ ⟶ X)), IsAffineOpen U₀ → W₀ ≤ U₀ → ⊤ ≤ χ ⁻¹ᵁ U₀ → (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ χ ⁻¹ᵁ U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ⊤ ≤ y w ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (y w) U f)) → (∃ T C : ℝ, ∀ w : ℂ, T < w.im → ∀ hy : ⊤ ≤ y w ⁻¹ᵁ W₀, ‖ev (y w) W₀ hy f₀‖ ≤ C) → ∀ h : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ W₀, ev (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) W₀ h f₀ ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range := by
  intro X U₀ W₀ f₀ χ y hU₀ hWU hχ harc hbd h
  have hηW : (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) (default : PrimeSpectrum (LaurentSeries ℂ)) ∈ W₀ :=
    h trivial
  obtain ⟨s, hsW, hsη⟩ := hU₀.exists_basicOpen_le (V := W₀) ⟨_, hηW⟩ (hWU hηW)
  obtain ⟨n, t, ht⟩ := exists_eq_pow_mul_of_isAffineOpen X U₀ hU₀ s
    ((X.presheaf.map (homOfLE hsW).op).hom f₀)
  have hsU : X.basicOpen s ≤ U₀ := X.basicOpen_le s

  have key : ∀ (A : Type) [CommRing A] (z : Sp A ⟶ X) (hz : ⊤ ≤ z ⁻¹ᵁ X.basicOpen s),
      valR z U₀ (t * s) = valR z U₀ (s ^ (n + 1)) * valR z W₀ f₀ := by
    intro A _ z hz
    have hzU : ⊤ ≤ z ⁻¹ᵁ U₀ := GlobalTheory.FlagMod.le_preimage_mono hsU hz
    have e := congrArg (GlobalTheory.HolHom.evalHom z _ hz) ht
    rw [map_mul, map_pow] at e
    simp only [← GlobalTheory.HolHom.valR_eq z _ hz] at e
    erw [GlobalTheory.HolHom.valR_res z hsU t hz, GlobalTheory.HolHom.valR_res z hsU s hz, GlobalTheory.HolHom.valR_res z hsW f₀ hz] at e
    rw [GlobalTheory.HolHom.valR_eq z U₀ hzU, GlobalTheory.HolHom.valR_eq z U₀ hzU, map_mul, map_pow,
      ← GlobalTheory.HolHom.valR_eq z U₀ hzU, ← GlobalTheory.HolHom.valR_eq z U₀ hzU, e]
    ring

  have hηs : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ X.basicOpen s := fun p _ => by
    obtain rfl : p = (default : PrimeSpectrum (LaurentSeries ℂ)) := Subsingleton.elim _ _
    exact hsη
  have hηU : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ U₀ := GlobalTheory.FlagMod.le_preimage_mono hsU hηs
  have hu : IsUnit (HahnSeries.ofPowerSeries ℤ ℂ (valR χ U₀ (s ^ (n + 1)))) := by
    rw [← GlobalTheory.HolHom.valR_spMap _ χ U₀ hχ, GlobalTheory.HolHom.valR_eq _ U₀ hηU, map_pow, ← GlobalTheory.HolHom.valR_eq _ U₀ hηU]
    exact ((GlobalTheory.ArcLie.le_basicOpen_iff_isUnit _ hηU s).1 hηs).pow _
  have kη := key _ _ hηs
  rw [GlobalTheory.HolHom.valR_spMap _ χ U₀ hχ, GlobalTheory.HolHom.valR_spMap _ χ U₀ hχ, valR_eq_ev _ W₀ h] at kη
  have hH : valR χ U₀ (s ^ (n + 1)) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu
    exact not_isUnit_zero hu
  obtain ⟨T₁, h₁⟩ := harc U₀ (t * s) hχ
  obtain ⟨T₂, h₂⟩ := harc U₀ (s ^ (n + 1)) hχ
  obtain ⟨T₃, C, h₃⟩ := hbd
  obtain ⟨Q, hQ⟩ := _root_.GlobalTheory.powerSeries_dvd_of_sum_bounded (valR χ U₀ (t * s)) (valR χ U₀ (s ^ (n + 1))) (max T₁ (max T₂ T₃)) C
    (fun w => valAt' (y w) U₀ (t * s)) (fun w => valAt' (y w) U₀ (s ^ (n + 1))) hH (fun w hw => by
      have hw1 : T₁ < w.im := lt_of_le_of_lt (le_max_left _ _) hw
      have hw2 : T₂ < w.im := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hw
      have hw3 : T₃ < w.im := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hw
      obtain ⟨hyU, hG⟩ := h₁ w hw1
      obtain ⟨-, hH'⟩ := h₂ w hw2
      refine ⟨hG, hH', fun hne => ?_⟩
      have hys : ⊤ ≤ y w ⁻¹ᵁ X.basicOpen s := by
        rw [GlobalTheory.HolHom.le_basicOpen_iff (y w) hyU s]
        intro h0
        apply hne
        rw [GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valR_eq _ _ hyU, map_pow]
        rw [GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valR_eq _ _ hyU] at h0
        rw [h0, zero_pow (Nat.succ_ne_zero n)]
      have hyW : ⊤ ≤ y w ⁻¹ᵁ W₀ := GlobalTheory.FlagMod.le_preimage_mono hsW hys
      show ‖valR (y w) U₀ (t * s)‖ ≤ C * ‖valR (y w) U₀ (s ^ (n + 1))‖
      rw [key ℂ (y w) hys, valR_eq_ev (y w) W₀ hyW, norm_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (h₃ w hw3 hyW) (norm_nonneg _))
  rw [hQ, map_mul] at kη
  exact ⟨Q, hu.mul_left_cancel kη⟩

end GlobalTheory.ArcReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

noncomputable section

namespace GlobalTheory.FlagEmb.PlkSpan

theorem indep_of_plk_ne_zero (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K)
    (h : plk u id ≠ 0) : LinearIndependent K u := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h
  set r := GlobalTheory.FlagEmb.plE N k q
  have hdet : (Matrix.of fun l l' => u l (r l')).det ≠ 0 := hq
  have hA := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  refine LinearIndependent.of_comp (LinearMap.funLeft K K r) ?_
  exact hA

theorem plk_ne_zero_of_indep (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K)
    (h : LinearIndependent K u) : plk u id ≠ 0 := by
  let Q : Matrix (Fin (N + 1)) (Fin k) K := (Matrix.of u).transpose
  have hinj : Function.Injective Q.mulVec := by
    intro x y hxy
    have h0 : Q.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have h1 : ∑ l, (x - y) l • u l = 0 := by
      funext r
      have := congrFun h0 r
      simp only [Q, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    have h2 := (Fintype.linearIndependent_iff.1 h) _ h1
    funext l
    exact sub_eq_zero.1 (h2 l)
  obtain ⟨Q', hQ'⟩ := GlobalTheory.matrix_exists_left_inverse_of_field Q hinj
  have hCB := GlobalTheory.FlagEmb.CauchyBinet.lform_plk K N k (Fin k) (Fin k) (fun l => Q' l) u id id
  have hM : (Matrix.of fun l l' => ∑ r, (fun l => Q' l) (id l') r * u (id l) r) = (Q' * Q).transpose := by
    ext l l'
    simp [Q, Matrix.mul_apply, mul_comm]
  rw [hM, hQ', Matrix.transpose_one, Matrix.det_one] at hCB
  intro h0
  rw [h0] at hCB
  simp at hCB

theorem plk_comb (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K) (T : Matrix (Fin k) (Fin k) K) :
    plk (fun l => ∑ j, T l j • u j) id = T.det • plk u id := by
  funext q
  simp only [plk, id, Pi.smul_apply, smul_eq_mul]
  rw [← Matrix.det_mul]
  congr 1
  ext l l'
  simp [Matrix.mul_apply, Finset.sum_apply]

theorem main : ∀ (K : Type) [Field K] (N k : ℕ) (u u' : Fin k → Fin (N + 1) → K), (plk u id ≠ 0 ↔ LinearIndependent K u) ∧ (LinearIndependent K u → ((LinearIndependent K u' ∧ Submodule.span K (Set.range u') = Submodule.span K (Set.range u)) ↔ ∃ r : Kˣ, plk u' id = (r : K) • plk u id)) := by
  intro K _ N k u u'
  refine ⟨⟨indep_of_plk_ne_zero K N k u, plk_ne_zero_of_indep K N k u⟩, fun hu => ⟨?_, ?_⟩⟩
  · rintro ⟨hu', hs⟩
    choose c hc using fun l => (Submodule.mem_span_range_iff_exists_fun K).1
      (hs ▸ Submodule.subset_span ⟨l, rfl⟩ : u' l ∈ Submodule.span K (Set.range u))
    have h1 := plk_comb K N k u (Matrix.of c)
    have h2 : (fun l => ∑ j, (Matrix.of c) l j • u j) = u' := funext hc
    rw [h2] at h1
    have hd : (Matrix.of c).det ≠ 0 := by
      intro h0
      exact plk_ne_zero_of_indep K N k u' hu' (by rw [h1, h0, zero_smul])
    exact ⟨Units.mk0 _ hd, h1⟩
  · rintro ⟨r, hr⟩
    have h0 := plk_ne_zero_of_indep K N k u hu
    have h0' : plk u' id ≠ 0 := by
      rw [hr]
      exact smul_ne_zero r.ne_zero h0
    have hr' : plk u id = (r : K)⁻¹ • plk u' id := by
      rw [hr, smul_smul, inv_mul_cancel₀ r.ne_zero, one_smul]
    refine ⟨indep_of_plk_ne_zero K N k u' h0', le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact mem_span_of_plk_eq_smul K N k u u' _ h0' hr l
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact mem_span_of_plk_eq_smul K N k u' u _ h0 hr' l

end GlobalTheory.FlagEmb.PlkSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDerivationAffineOpenEqFderivEtaleChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PointDer

open CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

def dualHom {A : Type} [CommRing A] (e : A →+* ℂ) (D : A →+ ℂ)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f) : A →+* DualNumber ℂ where
  toFun f := TrivSqZeroExt.inl (e f) + TrivSqZeroExt.inr (D f)
  map_one' := by
    have h1 : D 1 = 0 := by simpa using hm 1 1
    ext <;> simp [h1]
  map_mul' f f' := by ext <;> simp [hm, mul_comm]
  map_zero' := by ext <;> simp
  map_add' f f' := by ext <;> simp

@[simp] theorem dualHom_fst {A : Type} [CommRing A] (e : A →+* ℂ) (D : A →+ ℂ)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f) (f : A) : (dualHom e D hm f).fst = e f := by
  simp [dualHom]

@[simp] theorem dualHom_snd {A : Type} [CommRing A] (e : A →+* ℂ) (D : A →+ ℂ)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f) (f : A) : (dualHom e D hm f).snd = D f := by
  simp [dualHom]

theorem derivation_eq_zero_of_etale {k A : Type} [CommRing k] [CommRing A] {g : ℕ}
    (φ : MvPolynomial (Fin g) k →+* A) (hφ : φ.Etale) (e : A →+* ℂ) (D : A →+ ℂ)
    (h0 : ∀ a, D (φ (MvPolynomial.C a)) = 0)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f)
    (hX : ∀ i, D (φ (MvPolynomial.X i)) = 0) : D = 0 := by
  have hP : ∀ q, D (φ q) = 0 := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add q r hq hr => rw [map_add (f := _), map_add (f := _), hq, hr, add_zero]
    | mul_X q i hq => rw [map_mul, hm, hq, hX]; simp
  let F : A →+* DualNumber ℂ := dualHom e D hm
  let F₀ : A →+* DualNumber ℂ := (algebraMap ℂ (DualNumber ℂ)).comp e
  have hFF : ∀ q, F (φ q) = F₀ (φ q) := fun q => by
    ext <;> simp [F, F₀, hP, TrivSqZeroExt.algebraMap_eq_inl]
  let _ := φ.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) k) (DualNumber ℂ) := (F₀.comp φ).toAlgebra
  have _ : Algebra.Etale (MvPolynomial (Fin g) k) A := hφ
  let G : A →ₐ[MvPolynomial (Fin g) k] DualNumber ℂ := { F with commutes' := hFF }
  let G₀ : A →ₐ[MvPolynomial (Fin g) k] DualNumber ℂ := { F₀ with commutes' := fun q => rfl }
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have hG : G = G₀ := Algebra.FormallyUnramified.ext' (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom hnil G G₀
    (fun x => by simp [G, G₀, F, F₀])
  ext f
  have := congrArg (fun H : A →ₐ[MvPolynomial (Fin g) k] DualNumber ℂ => (H f).snd) hG
  simpa [G, G₀, F, F₀, TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.PointDer

namespace GlobalTheory.PointDer

open CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem exists_eq_fderiv : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (x₀ : CxPts p σ), x₀ ∈ c.e.source → ∀ (U : Y.affineOpens), x₀ ∈ CxPts.ptsIn p σ U.1 → ∀ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) → (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) → ∃ v : ReciprocityTheory.L2DbarEstimates.V n, ∀ g : Γ(Y, U.1), δ g = fderiv ℂ (CxPts.ev p σ U.1 g ∘ c.e.symm) (c.e x₀) v := by
  intro k _ Y p n σ c x₀ hx₀ U hU δ hδ0 hδm
  have hxc : x₀ ∈ ptsIn p σ c.U := c.source_subset hx₀
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 c.affine _
    ⟨mem_ptsIn.1 hU, mem_ptsIn.1 hxc⟩
  have hWc : Y.basicOpen g ≤ c.U := Y.basicOpen_le g
  have hWU : Y.basicOpen g ≤ U.1 := hfg ▸ Y.basicOpen_le f
  have hxW : x₀ ∈ ptsIn p σ (Y.basicOpen g) := mem_ptsIn.2 (hfg ▸ hxf)

  have hmU : ∀ a b, δ (a * b) = evHom hU a * δ b + evHom hU b * δ a := fun a b => by
    rw [hδm, ev_eq hU, ev_eq hU]
  let ψU := dualHom (evHom hU) δ hmU
  letI : Algebra Γ(Y, U.1) Γ(Y, Y.basicOpen g) := (resG Y hWU).toAlgebra
  haveI : IsLocalization.Away f Γ(Y, Y.basicOpen g) :=
    U.2.isLocalization_of_eq_basicOpen f (homOfLE hWU) hfg.symm
  have hfu : IsUnit (ψU f) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, dualHom_fst, isUnit_iff_ne_zero, ← ev_eq hU]
    exact (mem_ptsIn_basicOpen hU f).1 (mem_ptsIn.2 hxf)
  let ψW : Γ(Y, Y.basicOpen g) →+* DualNumber ℂ := IsLocalization.Away.lift f hfu
  have hψW (a : Γ(Y, U.1)) : ψW (resG Y hWU a) = ψU a := IsLocalization.Away.lift_eq f hfu a
  have hψW1 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp ψW = evHom hxW := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    change (ψW (resG Y hWU a)).fst = evHom hxW (resG Y hWU a)
    rw [hψW, dualHom_fst, ← ev_eq, ← ev_eq, ev_res _ hxW]
  have hfst (a : Γ(Y, Y.basicOpen g)) : (ψW a).fst = evHom hxW a := RingHom.congr_fun hψW1 a

  let v : ReciprocityTheory.L2DbarEstimates.V n := WithLp.toLp 2 (fun b => (ψW (resG Y hWc (c.x b))).snd)

  have hdW := fun a : Γ(Y, Y.basicOpen g) => c.differentiableAt_ev a hx₀ hxW
  let dW : Γ(Y, Y.basicOpen g) → ℂ := fun a => fderiv ℂ (ev p σ _ a ∘ c.e.symm) (c.e x₀) v
  have hdadd (a b) : dW (a + b) = dW a + dW b := by
    have e : ev p σ _ (a + b) ∘ c.e.symm = (ev p σ _ a ∘ c.e.symm) + (ev p σ _ b ∘ c.e.symm) :=
      funext fun _ => ev_add _ _ _
    simp only [dW, e, fderiv_add (hdW a) (hdW b), ContinuousLinearMap.add_apply]
  have hdmul (a b) : dW (a * b) = evHom hxW a * dW b + evHom hxW b * dW a := by
    have e : ev p σ _ (a * b) ∘ c.e.symm = (ev p σ _ a ∘ c.e.symm) * (ev p σ _ b ∘ c.e.symm) :=
      funext fun _ => ev_mul _ _ _
    simp only [dW, e, fderiv_mul (hdW a) (hdW b), Function.comp_apply, c.e.left_inv hx₀,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ← ev_eq hxW]
  have hn : ∀ᶠ w in 𝓝 (c.e x₀), c.e.symm w ∈ ptsIn p σ (Y.basicOpen g) :=
    Filter.eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn _)).mem_nhds
      (ChartGlue.mem_over c.e hx₀ hxW)) fun _ h => h.2

  let Dd : Γ(Y, Y.basicOpen g) →+ ℂ := AddMonoidHom.mk' (fun a => (ψW a).snd - dW a) fun a b => by
    simp only [map_add (f := _), TrivSqZeroExt.snd_add, hdadd]
    ring
  have hD : Dd = 0 := by
    refine derivation_eq_zero_of_etale ((resG Y hWc).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x))
      ?_ (evHom hxW) Dd ?_ ?_ ?_
    · have hR : (resG Y hWc).Etale := by
        letI : Algebra Γ(Y, c.U) Γ(Y, Y.basicOpen g) := (resG Y hWc).toAlgebra
        haveI : IsLocalization.Away g Γ(Y, Y.basicOpen g) :=
          c.affine.isLocalization_of_eq_basicOpen g (homOfLE hWc) rfl
        exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway g)
      exact RingHom.Etale.stableUnderComposition _ _ c.etale hR
    · intro a
      have e1 : (resG Y hWc) (MvPolynomial.eval₂Hom (algX p c.U) c.x (MvPolynomial.C a)) =
          resG Y hWU (algX p U.1 a) := by
        rw [MvPolynomial.eval₂Hom_C, ← RingHom.comp_apply, GlobalTheory.TopForm.resG_comp_algX,
          ← RingHom.comp_apply, GlobalTheory.TopForm.resG_comp_algX]
      have e2 : dW (resG Y hWU (algX p U.1 a)) = 0 := by
        have e : ev p σ _ (resG Y hWU (algX p U.1 a)) ∘ c.e.symm =ᶠ[𝓝 (c.e x₀)] fun _ => σ a := by
          filter_upwards [hn] with w hw
          rw [Function.comp_apply, ← RingHom.comp_apply, GlobalTheory.TopForm.resG_comp_algX]
          exact ev_algX hw a
        show fderiv ℂ _ _ v = 0
        rw [e.fderiv_eq]
        simp
      simp only [Dd, AddMonoidHom.mk'_apply, RingHom.comp_apply, e1, hψW, ψU, dualHom_snd, hδ0, e2, sub_zero]
    · intro a b
      simp only [Dd, AddMonoidHom.mk'_apply, map_mul, TrivSqZeroExt.snd_mul, hfst, hdmul, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
    · intro i
      have e2 : dW (resG Y hWc (c.x i)) = v i := by
        have e : ev p σ _ (resG Y hWc (c.x i)) ∘ c.e.symm =ᶠ[𝓝 (c.e x₀)]
            EuclideanSpace.proj (𝕜 := ℂ) i := by
          filter_upwards [hn, c.e.open_target.mem_nhds (c.e.map_source hx₀)] with w hw hwt
          rw [Function.comp_apply, ev_res hWc hw, ← c.apply_eq _ (c.e.map_target hwt) i,
            c.e.right_inv hwt]
          rfl
        simp only [dW, e.fderiv_eq, ContinuousLinearMap.fderiv]
        rfl
      simp only [Dd, AddMonoidHom.mk'_apply, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', e2]
      simp [v]
  refine ⟨v, fun a => ?_⟩
  have h1 := congrArg (fun D : Γ(Y, Y.basicOpen g) →+ ℂ => D (resG Y hWU a)) hD
  simp only [Dd, AddMonoidHom.mk'_apply, AddMonoidHom.zero_apply, hψW, dualHom_snd, sub_eq_zero] at h1
  rw [show δ a = (ψU a).snd from (dualHom_snd _ _ _ a).symm, h1]
  have e : ev p σ _ (resG Y hWU a) ∘ c.e.symm =ᶠ[𝓝 (c.e x₀)] ev p σ U.1 a ∘ c.e.symm := by
    filter_upwards [hn] with w hw
    exact ev_res hWU hw a
  simp only [dW, e.fderiv_eq]

end GlobalTheory.PointDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TraitOrder

theorem idlAlong_eq_map {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (χ : Sp R ⟶ X)
    (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
    idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
  have hx : χ (closedPoint R) ∈ U.1 := hle trivial
  unfold idlAlong
  rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
  congr 2

theorem idlAlong_comp {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
  have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
  rw [idlAlong_eq_map J χ ⟨U, hU⟩ hle, idlAlong_eq_map J _ ⟨U, hU⟩ hle', Ideal.map_map]
  congr 1
  have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
  rfl

theorem map_injective {R S : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S] [IsDomain S]
    [IsLocalRing S] (f : R →+* S) (hf : Function.Injective f) [IsLocalHom f] {I J : Ideal R}
    (h : I.map f = J.map f) : I = J := by
  letI := f.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Module.Flat R S := inferInstance
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) I, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) J]
  exact congrArg _ h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (e : g ≫ f = h) (m : SABMap t' t f) (m' : SABMap t'' t' g) : Nonempty (SABMap t'' t h) :=
  e ▸ ⟨(sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m').choose⟩

theorem cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (e : g ≫ f = h) (m : SABMap t' t f) (n : SABMap t'' t h) : Nonempty (SABMap t'' t' g) := by
  subst e
  exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n).choose⟩

end GlobalTheory.TraitOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackAnalytic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem IsLatFam.pullback_analytic : ∀ (m n g : ℕ) (B : Set (Fin n → ℂ)) (B' : Set (Fin m → ℂ))
    (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ),
    GlobalTheory.ShFam.Hor.LogCh.IsLatFam B K → IsOpen B' → AnalyticOnNhd ℂ φ B' → Set.MapsTo φ B' B →
      GlobalTheory.ShFam.Hor.LogCh.IsLatFam B' (fun b => K (φ b)) := by
  intro m n g B B' K φ hK hB' hφ hmaps
  obtain ⟨_, h2, h3, h4⟩ := hK
  let Ψ : (Fin m → ℂ) × (Fin g → ℂ) → (Fin n → ℂ) × (Fin g → ℂ) := fun q => (φ q.1, q.2)
  refine ⟨hB', fun b hb => h2 (φ b) (hmaps hb), ?_, ?_⟩
  · have hcont : ContinuousOn Ψ (B' ×ˢ (Set.univ : Set (Fin g → ℂ))) :=
      (hφ.continuousOn.comp continuousOn_fst
        (fun q (hq : q ∈ B' ×ˢ (Set.univ : Set (Fin g → ℂ))) => hq.1)).prodMk continuousOn_snd
    have hopen := hcont.isOpen_inter_preimage (hB'.prod isOpen_univ) h3
    convert hopen using 1
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true, Set.mem_preimage, Ψ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hmaps h1, h2⟩
    · rintro ⟨h1, _, h2⟩
      exact ⟨h1, h2⟩
  · intro b₀ hb₀ w₀ hw₀
    obtain ⟨ζ, hζ0, hζa, hev⟩ := h4 (φ b₀) (hmaps hb₀) w₀ hw₀
    refine ⟨fun b => ζ (φ b), hζ0, hζa.comp (hφ b₀ hb₀), ?_⟩
    have hΨ : ContinuousAt Ψ (b₀, w₀) :=
      ((hφ b₀ hb₀).continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
    exact hΨ.tendsto.eventually hev

end GlobalTheory.ShFam.Hor.LogCh
end

