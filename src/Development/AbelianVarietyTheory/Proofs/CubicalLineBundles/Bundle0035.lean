module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfGenericFibre
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieMetric

section Linear

variable {K : Type} [Field K] {g : ℕ}

def ofGram (G : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (hG : ∀ s, (G s).PosDef) : HermFam K (Fin g → K) where
  form s c c' := star (s ∘ c) ⬝ᵥ (G s).mulVec (s ∘ c')
  add_right s x y z := by
    rw [show s ∘ (y + z) = s ∘ y + s ∘ z from funext fun i => map_add s _ _, Matrix.mulVec_add, dotProduct_add]
  smul_right s a x y := by
    rw [show s ∘ (a • y) = s a • (s ∘ y) from funext fun i => map_mul s _ _, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul]
  conj_symm s x y := by
    change star _ = _
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, (hG s).isHermitian.eq, Matrix.dotProduct_mulVec]
  posDef s n v hv := by
    letI : Algebra K ℂ := s.toAlgebra
    have h1 : LinearIndependent ℂ (fun i => algebraMap K ℂ ∘ v i) := linearIndependent_algebraMap_comp_iff.2 hv
    have h2 := (hG s).conjTranspose_mul_mul_same (B := (Matrix.of fun i => s ∘ v i).transpose)
      (Matrix.mulVec_injective_iff.2 h1)
    convert h2 using 1
    ext i j
    rw [Matrix.mul_assoc]
    rfl

theorem ofGram_single (G : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (hG : ∀ s, (G s).PosDef) (s : K →+* ℂ) (i j : Fin g) :
    (ofGram G hG).form s (Pi.single i 1) (Pi.single j 1) = G s i j := by
  have e : ∀ i : Fin g, s ∘ (Pi.single i 1 : Fin g → K) = Pi.single i 1 := fun i => by
    ext k
    by_cases h : k = i <;> simp [h]
  simp [ofGram, e, ← Pi.single_star]

theorem form_sum_right (h : HermFam K (Fin g → K)) (s : K →+* ℂ) (x y : Fin g → K) :
    h.form s x y = ∑ j, s (y j) * h.form s x (Pi.single j 1) := by
  let f : (Fin g → K) →+ ℂ := AddMonoidHom.mk' (h.form s x) (h.add_right s x)
  have e : y = ∑ j, y j • Pi.single j (1 : K) := pi_eq_sum_univ' y
  refine (congrArg f e).trans ((map_sum f _ _).trans (Finset.sum_congr rfl fun j _ => h.smul_right s _ _ _))

theorem ext_single {h h' : HermFam K (Fin g → K)}
    (e : ∀ s i j, h.form s (Pi.single i 1) (Pi.single j 1) = h'.form s (Pi.single i 1) (Pi.single j 1)) : h = h' := by
  have e1 : ∀ s i y, h.form s (Pi.single i 1) y = h'.form s (Pi.single i 1) y := fun s i y => by
    rw [form_sum_right h, form_sum_right h']
    simp only [e]
  have e2 : h.form = h'.form := by
    funext s x y
    rw [form_sum_right h, form_sum_right h']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← h.conj_symm, ← h'.conj_symm, e1]
  cases h
  cases h'
  congr

theorem posDef_gram {n : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) {W : Fin n → Fin g → ℂ}
    (hW : LinearIndependent ℂ W) : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).PosDef := by
  have h1 : Hm.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx =>
    Complex.pos_iff.2 ⟨by simpa using hp (star x) (by simpa using hx), (hH.im_star_dotProduct_mulVec_self x).symm⟩
  have h2 := (h1.mul_mul_conjTranspose_same (B := Matrix.of W) (Matrix.vecMul_injective_iff.2 hW)).transpose.smul
    (a := (Real.pi : ℂ)) (by exact_mod_cast Real.pi_pos)
  rw [Matrix.mul_assoc] at h2
  exact h2

end Linear

theorem linearIndependent_of_isLieBasis {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g n : ℕ} (u : HolUnif A L g)
    (hu : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {v : Fin n → (epsR ℂ ⟶ A)} (hv : IsLieBasis v)
    {W : Fin n → Fin g → ℂ} (hW : ∀ i, u.IsDiff (W i) (v i)) : LinearIndependent ℂ W := by
  have key : ∀ c : Fin n → ℂ, ∃ w, IsTangent w ∧ IsLieComb c v w ∧ u.IsDiff (∑ i, c i • W i) w := fun c => by
    have h := UnifDifferential.isDiff_prod u (fun i => c i • W i) _
      (fun i => Chart.isTan_scale (c i) ((Chart.isTan_iff _).2 (hv.1 i)))
      (fun i => UnifDifferential.isDiff_scale u (hW i) (c i))
    exact ⟨_, (Chart.isTan_iff _).1 h.1, (Chart.isLieComb_iff c v _).2 rfl, h.2⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  obtain ⟨w, h1, h2, h3⟩ := key c
  obtain ⟨w', h1', h2', h3'⟩ := key 0
  rw [hc] at h3
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at h3'
  obtain rfl := (hu 0).unique ⟨h1, h3⟩ ⟨h1', h3'⟩
  exact congrFun ((hv.2 w h1).unique h2 h2')

theorem hermForm_eq (hU : ThetaUnifAV) {R : Type} [CommRing R] {P : Out.PolAV (Sp R)} {s : R →+* ℂ}
    {Q Q' : Out.PolAV (Sp ℂ)} {ψ : Q.A.left ⟶ P.A.left} {ψ' : Q'.A.left ⟶ P.A.left} (h : IsPolFibre s P Q ψ)
    (h' : IsPolFibre s P Q' ψ') {g g' : ℕ} {u : HolUnif Q.A Q.L g} {u' : HolUnif Q'.A Q'.L g'}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ}
    (hu : u.IsAH Hm χ) (hu' : u'.IsAH Hm' χ') {I : Type} {v : I → (epsR R ⟶ P.A)} (hv : ∀ i, IsTangent (v i))
    {w : I → (epsR ℂ ⟶ Q.A)} {w' : I → (epsR ℂ ⟶ Q'.A)} {W : I → Fin g → ℂ} {W' : I → Fin g' → ℂ}
    (hw : ∀ i, IsVecOver s ψ (v i) (w i) ∧ u.IsDiff (W i) (w i))
    (hw' : ∀ i, IsVecOver s ψ' (v i) (w' i) ∧ u'.IsDiff (W' i) (w' i)) (i j : I) :
    hermForm Hm (W i) (W j) = hermForm Hm' (W' i) (W' j) := by
  obtain ⟨e, he, heψ⟩ := grpPullback_iso h.2.1 h'.2.1
  obtain ⟨-, -, -, -, t1, t2, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q' g' u' Hm' χ' hu'
  obtain ⟨F, hF, -, hd, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L g g' u u' t1 t2
    e.hom he
  have hW : ∀ k, F (W k) = W' k := fun k => by
    obtain ⟨a, b⟩ := hd _ _ ((hw k).1.isTangent h.2.1 (hv k)) (hw k).2
    have c : w k ≫ e.hom = w' k := (existsUnique_isVecOver h'.2.1.1 (v k)).unique
      (by unfold IsVecOver; rw [Over.comp_left, Category.assoc, heψ]; exact (hw k).1) (hw' k).1
    rw [c] at a b
    exact (t1 _ a).unique b (hw' k).2
  obtain ⟨t, ht⟩ : LBIso (Q'.L.pull e.hom.left) Q.L :=
    LBIso.trans (pull_isLB Q'.isLB _) (pull_isLB P.isLB _) Q.isLB (PolFibre.lbIso_pull_comp h'.2.2 _).symm
      (heψ ▸ h.2.2)
  have := hermForm_pull_eq_of_lbIso_pow Q.A Q'.A Q.L Q'.L Q.isLB Q'.isLB g g' u u' Hm χ Hm' χ' hu hu' e.hom F hF 1 1
    ⟨LB.linCombIso t _ _, DVR.linCombIso_isGen t ht _ _⟩ (W i) (W j)
  simpa [hW] using this.symm

theorem exists_unique_isHerm : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), (∃ h : HermFam K (Fin F.P₀.g → K), F.IsHerm h) ∧ ∀ h h' : HermFam K (Fin F.P₀.g → K), F.IsHerm h → F.IsHerm h' → h = h' := by
  intro hU hL K _ _ P F
  refine ⟨?_, fun h h' H H' => ext_single fun s i j => ?_⟩
  · have key : ∀ s : K →+* ℂ, ∃ G : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ, G.PosDef ∧
        ∃ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A))
          (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (W : Fin F.P₀.g → Fin Q.g → ℂ),
          IsPolFibre s F.P₀ Q ψ ∧ u.IsAH Hm χ ∧ (∀ i, IsVecOver s ψ (F.v i) (v' i) ∧ u.IsDiff (W i) (v' i)) ∧
          ∀ i j, G i j = Real.pi * hermForm Hm (W j) (W i) := fun s => by
      obtain ⟨Q, ψ, h⟩ := exists_isPolFibre hL.polBaseChange s F.P₀
      haveI := F.P₀.isAb.comm
      haveI := Q.isAb.comm
      haveI := F.P₀.smoothDim
      obtain ⟨v', hb, hv'⟩ := exists_isLieBasis_baseChange K ℂ s F.P₀.A Q.A ψ h.2.1
        (SmoothOfRelativeDimension.smooth F.P₀.g _) _ F.v F.basis
      obtain ⟨rig, hrig⟩ := Q.rigid
      obtain ⟨u, Hm, χ, -, hA, -, hd, hd', -⟩ := hU Q rig hrig
      choose W hW using fun i => (hd _ (hb.1 i)).exists
      exact ⟨_, posDef_gram hA.1 hA.2.1 (linearIndependent_of_isLieBasis u hd' hb hW), Q, ψ, v', u, Hm, χ, W, h, hA,
        fun i => ⟨hv' i, hW i⟩, fun _ _ => rfl⟩
    choose G hG H using key
    refine ⟨ofGram G hG, fun s => ?_⟩
    simpa only [ofGram_single] using H s
  · obtain ⟨Q, ψ, v, u, Hm, χ, W, a, b, c, d⟩ := H s
    obtain ⟨Q', ψ', v', u', Hm', χ', W', a', b', c', d'⟩ := H' s
    rw [d, d', hermForm_eq hU a a' b b' F.basis.1 c c']

end GlobalTheory.CM.LieMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeEqValuationRingIffIsLocalization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem range_eq_valuationRing_iff_isLocalization :
    ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) (R : Type) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K] [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) R K], (∀ y : K, y ∈ Set.range (algebraMap R K) ↔ p.valuation K y ≤ 1) ↔ IsLocalization p.asIdeal.primeCompl R := by
  intro K _ _ p R _ _ _ _ _ _
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have htow : ∀ a : 𝓞 K, algebraMap R K (algebraMap (𝓞 K) R a) = algebraMap (𝓞 K) K a :=
    fun a => (IsScalarTower.algebraMap_apply (𝓞 K) R K a).symm
  have hone : ∀ s : p.asIdeal.primeCompl, p.valuation K (algebraMap (𝓞 K) K s) = 1 :=
    fun s => (p.valuation_eq_one_iff_notMem (K := K)).2 s.2
  have hne : ∀ s : p.asIdeal.primeCompl, algebraMap (𝓞 K) K s ≠ 0 := by
    intro s h
    have := hone s
    rw [h, map_zero] at this
    exact zero_ne_one this
  constructor
  · intro h
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · intro s
      obtain ⟨r, hr⟩ := (h (algebraMap (𝓞 K) K s)⁻¹).2 (by rw [map_inv₀, hone s, inv_one])
      refine IsUnit.of_mul_eq_one r (hinj ?_)
      rw [map_mul, htow, hr, map_one, mul_inv_cancel₀ (hne s)]
    · intro z
      obtain ⟨n, d, hnd⟩ := p.exists_primeCompl_mul_eq_of_integer (algebraMap R K z)
        ((h _).1 ⟨z, rfl⟩)
      refine ⟨(n, d), hinj ?_⟩
      rw [map_mul, htow, htow]
      exact hnd
    · intro x y hxy
      refine ⟨1, ?_⟩
      have h2 : algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K y := by
        rw [← htow, ← htow, hxy]
      rw [IsFractionRing.injective (𝓞 K) K h2]
  · intro h y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj p.asIdeal.primeCompl z
      have h2 := congrArg (fun t => p.valuation K (algebraMap R K t)) hnd
      simp only [map_mul, htow, hone] at h2
      rw [(_root_.mul_one _).symm.trans h2]
      exact p.valuation_le_one n
    · intro hy
      obtain ⟨n, d, hnd⟩ := p.exists_primeCompl_mul_eq_of_integer y hy
      refine ⟨IsLocalization.mk' R n d, ?_⟩
      apply mul_right_cancel₀ (hne d)
      rw [hnd, ← htow, ← htow, ← map_mul, IsLocalization.mk'_spec]

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TripleModel

open GlobalTheory.PrimNorm GlobalTheory.MulPull

section Charts

variable {Y Y' : Scheme.{0}}

end Charts

section Cubical

theorem isPullCubical_of_lbIso (hG : Out.GlobalFnsSt) {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G']
    [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (hA : IsAbelianScheme G') {f : S' ⟶ S} {α : G'.left ⟶ G.left}
    (gp : IsGrpPullback G' G f α) {L' : RigLB G'} {L : RigLB G}
    (c' : CubicalStr G' L') (c : CubicalStr G L) (h : LBIso L'.L (L.L.pull α)) :
    (cubeMapOf gp).IsPullCubical c' c := by
  obtain ⟨w, hw⟩ := h
  have hw' := (isGen_iff w).1 hw
  obtain ⟨a, ha, hm⟩ := DegPull.exists_pmaps (K := PUnit) hw' L.isLB L'.isLB (φ' := fun _ => eSec G')
    (φ := fun _ => eSec G) (ε := fun _ => 1) (cubeMapOf gp).e (fun _ => (cubeMapOf gp).e_comm) L.rig L.rigGen
  obtain ⟨u, hu⟩ := HeckePoint.exists_unit_ratio L'.isLB a L'.rig ha L'.rigGen
  let w₁ : LB.Iso L'.L (L.L.pull α) :=
    ⟨fun p => w.s p * res (U := G'.hom ⁻¹ᵁ ⊤) (fun _ _ => trivial) (pullU G'.hom ⊤ u)⟩
  have g₁ : ∀ (Y : Scheme.{0}) (f : Y ⟶ G'.left) (y : Y) j k, α (f y) ∈ L.L.U j → f y ∈ L'.L.U k →
      gw w₁ f y j k = gw w f y j k * gm (f ≫ G'.hom) y ⊤ u := fun Y f y j k hj hk =>
    (map_mul _ _ _).trans (congrArg _ ((gm_res f y _ (show f y ∈ (L.L.pull α).U (fun _ => j) ⊓ L'.L.U k from
      ⟨mem_pull.2 hj, hk⟩) _).trans (gm_pull f G'.hom y ⊤ trivial u)))
  have hw₁ : PGen w₁ := fun Y f y j j' k k' hj hj' hk hk' => by
    rw [g₁ Y f y j k hj hk, g₁ Y f y j' k' hj' hk', hw' Y f y j j' k k' hj hj' hk hk', _root_.mul_assoc]
  refine (isPullCubical_iff _ c c').2 ⟨w₁, hw₁, fun Z r z p q hp hq => ?_, ?_⟩
  · refine (hm Z r z p q hp hq).trans ?_
    have e : (r ≫ eSec G') ≫ G'.hom = r := by
      rw [Category.assoc, show eSec G' ≫ G'.hom = 𝟙 _ from Over.w η[G'], Category.comp_id]
    have e₂ := g₁ Z (r ≫ eSec G') z _ _ (hp default) (hq default)
    rw [e] at e₂
    rw [hu Z r z q (Set.mem_iInter.2 hq), Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one]
    exact (_root_.mul_assoc _ _ _).symm.trans (congrArg (· * _) e₂.symm)
  · let e : 𝟙_ (Over S') ⟶ G3 G' := lift 1 (lift 1 1)
    have s₁ := (hG _ _ hA).2
    have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ α = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
      fun I => (cubeMapOf gp).psum_comm I.down
    refine EvenPull.pmaps_of_section (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε) hw₁ L.isLB L'.isLB
      (cubeMapOf gp).F3 hψ c'.t c'.isGen
      c.t c.isGen (G3 G').hom e.left (Over.w e) (AbLaw.Cube.surj_tensor hG hA (AbLaw.Cube.surj_tensor hG hA s₁))
      (fun y J J' hJ hJ' => ?_)
    have a₁ : e.left ≫ (cubeMapOf gp).F3 =
        (lift (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) (lift 1 1)).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      have o := congrArg (fun q => q.left) (map_one (pushHom gp (𝟙_ (Over S'))))
      have e₁ : e ≫ x3 G' i = 1 := by fin_cases i <;> simp [e, x3]
      have e₂ : lift (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) (lift 1 1) ≫ x3 G i = 1 := by
        fin_cases i <;> simp [x3]
      rw [e₁, e₂]
      exact o
    have b₁ := (isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ).face 1 1
    have b₂ := (isCub_cubV c' (T := 𝟙_ (Over S')) hJ').face 1 1
    have b₃ := prod_cub (1 : 𝟙_ (Over S') ⟶ G') 1 1 (fun ψ => gw w₁ ψ y (J (ψ ≫ α)) (J' ψ))
    refine Eq.trans ((congrArg (fun q => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t q y J) a₁).trans b₁)
      (Eq.symm ?_)
    refine (congrArg₂ (· * ·) b₃ b₂).trans ?_
    simp

end Cubical

section Ample

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

end Ample

section Extend

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Over (Sp R)} [GrpObj A] {B : Over (Sp K)} [GrpObj B] {φ : B.left ⟶ A.left} {L : LB A.left} {L' : LB B.left}

end Extend

section Points

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B] {j : S' ⟶ S} {φ : B.left ⟶ A.left}

end Points

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (hLaws : Out.Laws) (t₀ : SAB H (Sp K)) {A : Over (Sp R)} [GrpObj A] {φ : t₀.G.left ⟶ A.left}
  (hA : IsAbelianScheme A) (gp : IsGrpPullback t₀.G A (spMap (algebraMap R K)) φ)
  {L : LB A.left} (hL : L.IsLB) (hr : Out.Rigidified A L) (i : LBIso t₀.PP.L (L.pull φ))

include hLaws hA gp hL hr i

end Triple

end GlobalTheory.TripleModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersActionInjectiveOnAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.Faithful

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O]

theorem act_zero (act : OAct O G) : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := act.act 0) (by rw [← h, _root_.mul_one])

theorem act_natCast (act : OAct O G) (n : ℕ) : act.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]

theorem act_mul_eq_one (act : OAct O G) {c : O} (hc : act.act c = 1) (d : O) : act.act (d * c) = 1 := by
  rw [act.mul, hc, MonObj.comp_one]

theorem pow_eq_one_of_act (act : OAct O G) {n : ℕ} (hn : act.act (n : O) = 1) {T : Over S} (x : T ⟶ G) :
    x ^ n = 1 := by
  have h : x ≫ (𝟙 G ^ n) = x ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  rw [← h, ← act_natCast act, hn, MonObj.comp_one]

end

theorem act_injective : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), 1 ≤ P.g → Function.Injective act.act := by
  intro hL E _ _ K _ _ P act hg a b hab
  by_contra hne
  have hc0 : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hc : act.act (a - b) = 1 := by
    have h := act.add (a - b) b
    rw [sub_add_cancel, hab] at h
    exact mul_right_cancel (b := act.act b) (by rw [← h, _root_.one_mul])
  set n : ℕ := Ideal.absNorm (Ideal.span {a - b}) with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {a - b}))
  have h1 : act.act (n : 𝓞 E) = 1 := by
    rw [hn, ← hd]; exact act_mul_eq_one act hc d
  let k := AlgebraicClosure K
  let t : Spec (CommRingCat.of k) ⟶ Sp (𝓞 K) :=
    Spec.map (CommRingCat.ofHom ((algebraMap K k).comp (algebraMap (𝓞 K) K)))
  haveI : CharZero k := charZero_of_injective_algebraMap (algebraMap K k).injective
  have key : ∀ m : ℕ, 1 ≤ m → Nat.card (Over.mk t ⟶ P.A) = (n * m) ^ (2 * P.g) := by
    intro m hm
    have hnm : n * m ≠ 0 := Nat.mul_ne_zero hn0 (by omega)
    obtain ⟨-, -, -, -, h⟩ := hL.mulN _ P (n * m) (Nat.one_le_iff_ne_zero.mpr hnm)
    rw [← h k t (Nat.cast_ne_zero.mpr hnm)]
    refine (Nat.card_congr (Equiv.subtypeUnivEquiv fun x => ?_)).symm
    rw [pow_mul, pow_eq_one_of_act act h1, one_pow]
  have e := (key 1 le_rfl).symm.trans (key 2 (by norm_num))
  have := Nat.pow_left_injective (by omega : 2 * P.g ≠ 0) e
  omega

end GlobalTheory.LamF.Faithful
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.RosLam

theorem form_rosati {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (f g : G ⟶ G)
    {V : Type} [CommGroup V] (k : ((G ⊗ G).left ⟶ G.left) → V) :
    (∏ I : ULift.{0} (Finset (Fin 2)),
        k (psum G ![fst G G ≫ f, snd G G] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card))) /
      (∏ I : ULift.{0} (Finset (Fin 2)),
        k (psum G ![fst G G, snd G G ≫ g] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card))) =
      ∏ i, k (Out.rosatiφ G f g i) ^ Out.rosatiε i := by
  have p := prod_ros f g (fst G G) (snd G G) k
  rw [lift_fst_snd] at p
  simp only [Over.id_left, Category.id_comp] at p
  rw [p, GlobalTheory.NormRos.prod_square, GlobalTheory.NormRos.prod_square]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_div]
  abel

theorem lbIso_of_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (f g : G ⟶ G) (t : LB.Gen (LB.LinComb L (Out.rosatiφ G f g) Out.rosatiε)) (ht : t.IsGen) :
    LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) := by
  obtain ⟨Pic, _, cl, pl, h₁, h₂, -, -, h₅, -⟩ := GlobalTheory.CechPicMul.exists_picardGroup
  obtain ⟨a, a'⟩ := h₅ _ _ L hL _ (Out.rosatiφ G f g) Out.rosatiε
  obtain ⟨b, b'⟩ : (cubeLB G ![fst G G ≫ f, snd G G] L).IsLB ∧ cl (cubeLB G ![fst G G ≫ f, snd G G] L) = _ :=
    h₅ _ _ L hL _ _ _
  obtain ⟨c, c'⟩ : (cubeLB G ![fst G G, snd G G ≫ g] L).IsLB ∧ cl (cubeLB G ![fst G G, snd G G ≫ g] L) = _ :=
    h₅ _ _ L hL _ _ _
  refine (h₁ _ _ _ b c).1 ?_
  have e := ((h₂ _ _ a).2 ⟨t, ht⟩).symm.trans a'
  rw [b', c', ← div_eq_one, e]
  have key := form_rosati f g (V := Multiplicative (FreeAbelianGroup ((G ⊗ G).left ⟶ G.left)))
    (fun ψ => Multiplicative.ofAdd (FreeAbelianGroup.of ψ))
  have k := congrArg (AddMonoidHom.toMultiplicativeLeft
    (FreeAbelianGroup.lift fun ψ : (G ⊗ G).left ⟶ G.left => Additive.ofMul (pl ψ (cl L)))) key
  simpa only [map_div, map_prod, map_zpow, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, toAdd_ofAdd,
    FreeAbelianGroup.lift_apply_of, toMul_ofMul] using k

theorem rosatiAdj_iff_lamEq : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (f g : P.A ⟶ P.A), IsMonHom f → IsMonHom g → (Out.RosatiAdj P.A P.L f g ↔ LamEq P.L f (𝟙 P.A) P.L (𝟙 P.A) g) := by
  intro hG S P f g hf hg
  have := P.isAb.comm
  unfold LamEq
  rw [Category.comp_id, Category.comp_id]
  constructor
  · intro h
    obtain ⟨u, hu, -⟩ := exists_ros hG P.isAb P.isLB f g h
    exact lbIso_of_gen P.isLB f g u hu
  · intro h s
    obtain ⟨t, ht⟩ := GlobalTheory.NormRos.exists_gen_rosati P.isLB f g h
    exact ⟨⊤, trivial, LB.pullGen P.L _ _ t _, DVR.pullGen_isGen _ _ _ _ ht _⟩

end GlobalTheory.RosLam
end

