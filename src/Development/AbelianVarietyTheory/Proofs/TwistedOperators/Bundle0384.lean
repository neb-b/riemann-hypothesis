module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralScalarOfPulledBackGeneratorExtendsModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0241
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0811
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0371

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentPartCompletedLatticeLocalChart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

open scoped TensorProduct

namespace GlobalTheory.EPartChart

open IsDedekindDomain Formalism.L2.NTheta

theorem int_smul_mem_hat (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    a • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction ha using AddSubgroup.closure_induction generalizing y with
  | mem w hw =>
    obtain ⟨b, hb, x, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, m, hm, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨b * c, fun v => ?_, x • m, L.smul_mem x hm, ?_⟩
      · exact mul_mem (hb v) (hc v)
      · funext i
        simp [Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ h h' => rw [add_smul]; exact add_mem (h hy) (h' hy)
  | neg a _ h => rw [neg_smul]; exact neg_mem (h hy)

theorem mem_Ov_iff {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    t ∈ Formalism.UG.Ov F v ↔ Valued.v t ≤ 1 := Iff.rfl

theorem exists_local_gen {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} (φ : E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (hφ : ∀ o : 𝓞 E, φ (o : E) ∈ Formalism.UG.Ov F v) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    ∃ α ∈ I, α ≠ 0 ∧ ∀ a ∈ I, φ a * (φ α)⁻¹ ∈ Formalism.UG.Ov F v := by
  classical
  obtain ⟨S, hS⟩ := FractionalIdeal.fg_of_isNoetherianRing le_rfl I
  have hSI : ∀ a ∈ S, a ∈ I := fun a ha => by
    rw [← FractionalIdeal.mem_coe, ← hS]; exact Submodule.subset_span ha
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hI
    rw [← FractionalIdeal.coeToSubmodule_inj, ← hS, Finset.coe_empty, Submodule.span_empty]
    simp
  obtain ⟨α, hαS, hmax⟩ := Finset.exists_max_image S (fun a => Valued.v (φ a)) hne
  have hα0 : α ≠ 0 := by
    rintro rfl
    apply hI
    rw [← FractionalIdeal.coeToSubmodule_inj, ← hS, FractionalIdeal.coe_zero, eq_bot_iff, Submodule.span_le]
    intro a ha
    have h1 := hmax a ha
    rw [map_zero, Valuation.map_zero, le_zero_iff, Valuation.zero_iff, map_eq_zero_iff φ φ.injective] at h1
    simp [h1]
  refine ⟨α, hSI α hαS, hα0, fun a ha => ?_⟩
  rw [← FractionalIdeal.mem_coe, ← hS] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rw [mem_Ov_iff, Valuation.map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ (hmax a ha) zero_le'
  | zero => rw [map_zero, zero_mul]; exact zero_mem _
  | add a b _ _ h h' => rw [map_add (f := _), add_mul]; exact add_mem h h'
  | smul o a _ h =>
    rw [Algebra.smul_def, map_mul, mul_assoc]
    exact mul_mem (hφ o) h

theorem tmul_vec_mul {D : D7} {n : ℕ} (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (a : D.host.E) (c : Fin n → D.host.E) :
    (fun i => b ⊗ₜ[D.host.F] (a • c) i) = finPart D (incA D a) • (fun i => b ⊗ₜ[D.host.F] c i) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  change _ = ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] a) * _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem smul_hat_latG_one {D : D7} (V : HSp D) {c : GlobalTheory.SplitPlace.RF D}
    (hc : ∀ a ∈ D.host.AA, c * finPart D (incA D a) ∈ intAE D) :
    ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)),
      c • z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨-, -, -, -, -, h6c⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hoi : ∀ o : 𝓞 D.host.E, finPart D (incA D (o : D.host.E)) ∈ intAE D := fun o =>
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, o, rfl⟩
  intro z hz
  unfold GlobalTheory.AdLat.hat at hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    rw [SetLike.mem_coe, h6c] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, c', hc', rfl⟩ := hx
      rw [tmul_vec_mul, smul_smul]
      exact int_smul_mem_hat D _ (hc a ha) (AddSubgroup.subset_closure ⟨b, hb, c', hc', rfl⟩)
    | zero =>
      have : (fun i => b ⊗ₜ[D.host.F] (0 : Fin V.rank → D.host.E) i) = 0 := by
        funext i; simp
      rw [this, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : (fun i => b ⊗ₜ[D.host.F] (x + y) i) =
          (fun i => b ⊗ₜ[D.host.F] x i) + (fun i => b ⊗ₜ[D.host.F] y i) := by
        funext i; simp [TensorProduct.tmul_add]
      rw [this, smul_add]; exact add_mem hx hy
    | smul o x _ hx =>
      have : (fun i => b ⊗ₜ[D.host.F] (o • x) i) = (fun i => b ⊗ₜ[D.host.F] ((o : D.host.E) • x) i) := rfl
      rw [this, tmul_vec_mul, smul_comm]
      exact int_smul_mem_hat D _ (hoi o) hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem smul_hat_latC {D : D7} (V : HSp D) {α : D.host.E} (hα : α ∈ D.host.AA)
    {z : Fin V.rank → GlobalTheory.SplitPlace.RF D}
    (hz : z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) :
    finPart D (incA D α) • z ∈ GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨-, -, -, -, -, h6c⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hs : ∀ x ∈ (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)),
      α • x ∈ (latG V 1 : Set (Fin V.rank → D.host.E)) := by
    intro x hx
    rw [SetLike.mem_coe, h6c]
    exact Submodule.subset_span ⟨α, hα, x, hx, rfl⟩
  exact GlobalTheory.AdLat.Scale.smul_mem_hat hs hz

theorem mem_latGHat_iff {D : D7} (V : HSp D) (x : GA D V) (ef : GlobalTheory.SplitPlace.RF D) (y : Fin V.rank → GlobalTheory.SplitPlace.RF D) :
    ef • y ∈ latGHat V x ↔
      ef • (GlobalTheory.SplitPlace.fm V x⁻¹ *ᵥ y) ∈ GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨-, -, -, h4x, -, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V x
  rw [← SetLike.mem_coe, h4x]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have : ef • (GlobalTheory.SplitPlace.fm V x⁻¹ *ᵥ y) = z := by
      rw [← Matrix.mulVec_smul, ← hzy]
      exact GlobalTheory.SplitPlace.fm_inv_vec V x z
    rwa [this]
  · intro h
    refine ⟨_, h, ?_⟩
    change GlobalTheory.SplitPlace.fm V x *ᵥ _ = _
    rw [Matrix.mulVec_smul, GlobalTheory.SplitPlace.fm_vec_inv]

end GlobalTheory.EPartChart

namespace GlobalTheory.EPartChart

open IsDedekindDomain Formalism.L2.NTheta

theorem chart_coord {D : D7} {V : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (B : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v))
    (τ : GlobalTheory.SplitPlace.RF D) (x : GA D V) (y : Fin V.rank → GlobalTheory.SplitPlace.RF D) :
    (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ (fun j => π ((τ • GlobalTheory.SplitPlace.fm V x⁻¹ *ᵥ y) j)) =
      (π τ • ((GlobalTheory.SplitPlace.comp V π B x⁻¹).1 * (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1)) *ᵥ
        fun j => π (y j) := by
  rw [GlobalTheory.SplitPlace.map_mulVec (π := π) (GlobalTheory.SplitPlace.fm V x⁻¹) τ y]
  have hM : (GlobalTheory.SplitPlace.comp V π B x⁻¹).1 * (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 =
      (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 * (GlobalTheory.SplitPlace.fm V x⁻¹).map π := by
    rw [GlobalTheory.SplitPlace.comp_val, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [hM, Matrix.smul_mulVec, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec]

theorem smul_eq_idem {R : Type} [CommRing R] {n : ℕ} (e τ : R) (he : e * e = e) (w : Fin n → R) :
    e • (τ • w) = (e * τ) • (e • w) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination (-(τ * w i)) * he

theorem smul_eq_inv {R : Type} [CommRing R] {n : ℕ} (a τ e : R) (h : a * τ = 1) (w : Fin n → R) :
    e • w = a • (e • (τ • w)) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination (-(e * w i)) * h


set_option maxHeartbeats 1000000 in
theorem latGHat_chart : ∀ (D : D7) (V : HSp D) (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D)
    (B : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)), e * e = e →
    (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    (∀ y : Fin V.rank → GlobalTheory.SplitPlace.RF D, (fun i => finPart D e * y i) ∈ LamHat V ↔
      ∀ i, ((B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    ∃ t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v, t ≠ 0 ∧ ∀ (x : GA D V) (y : Fin V.rank → GlobalTheory.SplitPlace.RF D),
      finPart D e • y ∈ latGHat V x ↔
        ∀ i, ((t • ((GlobalTheory.SplitPlace.comp V π B x⁻¹).1 * (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1)) *ᵥ
          fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  intro D V e v π s B he h2 h3 h4 hB
  have hee : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he]
  have hei : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he
  have hoi : ∀ o : 𝓞 D.host.E, finPart D (incA D (o : D.host.E)) ∈ intAE D := fun o =>
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, o, rfl⟩
  have hφo : ∀ o : 𝓞 D.host.E, ((π.comp (finPart D)).comp (incA D)) (o : D.host.E) ∈ Formalism.UG.Ov D.host.F v :=
    fun o => (h4 _).1 (GlobalTheory.HeckeConj.mul_mem_intAE D hei (hoi o))
  obtain ⟨α, hαA, hα0, hαg⟩ := exists_local_gen ((π.comp (finPart D)).comp (incA D)) hφo D.host.AA
    (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D)
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = finPart D (incA D α⁻¹) := ⟨_, rfl⟩
  have hατ : finPart D (incA D α) * τ = 1 := by
    rw [hτ, ← map_mul, ← map_mul, mul_inv_cancel₀ hα0, map_one, map_one]
  have hsc : ∀ a ∈ D.host.AA, finPart D e * τ * finPart D (incA D a) ∈ intAE D := by
    intro a ha
    rw [mul_assoc]
    refine (h4 _).2 ?_
    have e1 : τ * finPart D (incA D a) = finPart D (incA D (a * α⁻¹)) := by
      rw [hτ, ← map_mul, ← map_mul, mul_comm]
    rw [e1]
    have h : ((π.comp (finPart D)).comp (incA D)) (a * α⁻¹) ∈ Formalism.UG.Ov D.host.F v := by
      rw [map_mul, map_inv₀]; exact hαg a ha
    exact h
  have key : ∀ w : Fin V.rank → GlobalTheory.SplitPlace.RF D,
      finPart D e • w ∈ GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)) ↔
        finPart D e • (τ • w) ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    intro w
    constructor
    · intro h
      rw [smul_eq_idem _ τ hee w]
      exact smul_hat_latG_one V hsc _ h
    · intro h
      rw [smul_eq_inv _ τ (finPart D e) hατ w]
      exact smul_hat_latC V hαA h
  refine ⟨π τ, right_ne_zero_of_mul_eq_one (a := π (finPart D (incA D α))) (by rw [← map_mul, hατ, map_one]),
    fun x y => ?_⟩
  rw [mem_latGHat_iff, key, ← SetLike.mem_coe, ← GlobalTheory.LatDual.lamHat_eq_hat V, SetLike.mem_coe]
  refine (hB (τ • GlobalTheory.SplitPlace.fm V x⁻¹ *ᵥ y)).trans ?_
  rw [chart_coord]

end GlobalTheory.EPartChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralScalarOfPulledBackGeneratorExtendsModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_scalar_of_pulledBack_generator_extends_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (I : IntData Xo c T io y.1) (I' : IntData Xo c T io y'.1) (f : Fib Xo (xOf y) ⟶ Fib Xo (xOf y')) (F : I.G.G ⟶ I'.G.G) (F' : I'.G.G ⟶ I.G.G) (N M : ℕ) (a : T.Fr) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))), IsMonHom F → IsMonHom F' → Ext I.m1 I.m2 I'.m1 I'.m2 f F → F' ≫ F = 𝟙 _ ^ N → IsUnit (N : T.V) → letI := io.toAlgebra; IsPullOf M f a y'.1.s t → Reg I M t → a ∈ Set.range (algebraMap T.V T.Fr) := by
  first | exact @GlobalTheory.HkIntegral.PullScalar.mem_range_of_reg | exact GlobalTheory.HkIntegral.PullScalar.mem_range_of_reg | (intros; apply GlobalTheory.HkIntegral.PullScalar.mem_range_of_reg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviFactorScalarsAutomorphicCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LeviChar

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

theorem detPow_pos' {D : D7} {r : ℕ} (a : GL (Fin r) (AE D)) (n : ℕ) : 0 < GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
  apply Real.rpow_pos_of_pos
  exact NNReal.coe_pos.2 (pos_iff_ne_zero.2
    ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (GlobalTheory.Doubling.absE D.host.F D.host.E)).ne_zero)

theorem detPow_mul' {D : D7} {r : ℕ} (a b : GL (Fin r) (AE D)) (n : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow (a * b) n = GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n * GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow b n := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
  rw [map_mul, map_mul, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]

theorem detPow_one' {D : D7} {r : ℕ} (n : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow (1 : GL (Fin r) (AE D)) n = 1 := by
  have h := detPow_mul' (1 : GL (Fin r) (AE D)) 1 n
  rw [mul_one] at h
  exact mul_left_cancel₀ (detPow_pos' 1 n).ne' (h.symm.trans (mul_one _).symm)

theorem continuous_detPow' {D : D7} {r : ℕ} (n : ℕ) :
    Continuous fun a : GL (Fin r) (AE D) => GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
  have h1 : Continuous fun a : GL (Fin r) (AE D) => Matrix.GeneralLinearGroup.det a :=
    Matrix.GeneralLinearGroup.continuous_det
  have h2 := (GlobalTheory.Doubling.continuous_absE (F := D.host.F) (E := D.host.E))
  exact (NNReal.continuous_coe.comp (h2.comp h1)).rpow_const (fun _ => Or.inr (by positivity))



open GlobalTheory.MixModel in
theorem levi_scalars_autChar : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (χS' χT' : (AE D)ˣ →* Circle) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V' W χS' χT' ω' → ∃ (μa : GL (Fin r) (AE D) →* Circle) (ξ : GA D V' →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.IsAutCharGL r μa ∧ GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.IsAutCharU V' ξ ∧ ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, 1) f) = ((μa a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ) * (ξ g' : ℂ)) • ω' (g', 1) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) := by
  intro D V V' W r C B hs ψ χS χT ω hω χS' χT' ω' hω'
  obtain ⟨d, hdC, hdB, hker⟩ := _root_.GlobalTheory.WittSect.exists_hypDec_mem_NI D V V' r C B hs
  obtain ⟨μ₀, 𝓨₀, h₀⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank r
  have hind := fun f hf μ 𝓨 (hμ : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨) =>
    _root_.GlobalTheory.TowerRestrict.res_indep_covol D V V' W r C B hs d hdC hdB ψ f hf μ₀ μ 𝓨₀ 𝓨 h₀ hμ

  let s : GL (Fin r) (AE D) → GA D V' → GA D V := fun a g' => d.levi a * d.emb0 g'
  have hsC : ∀ a g', HMul.hMul (mt V (s a g')) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val := by
    intro a g'
    subst hdC
    show mt V (d.levi a * d.emb0 g') * d.jX = d.jX * a.1
    rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.levi_jX]
  have hsB : ∀ a g', HMul.hMul (mt V (s a g')) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (mt V' g') := by
    intro a g'
    subst hdB
    show mt V (d.levi a * d.emb0 g') * d.j0 = d.j0 * mt V' g'
    rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic]
  have hsmul : ∀ a₁ g₁ a₂ g₂, s (a₁ * a₂) (g₁ * g₂) = s a₁ g₁ * s a₂ g₂ := by
    intro a₁ g₁ a₂ g₂
    show d.levi (a₁ * a₂) * d.emb0 (g₁ * g₂) = d.levi a₁ * d.emb0 g₁ * (d.levi a₂ * d.emb0 g₂)
    rw [map_mul, map_mul, show d.levi a₁ * d.emb0 g₁ * (d.levi a₂ * d.emb0 g₂) =
      d.levi a₁ * (d.emb0 g₁ * d.levi a₂) * d.emb0 g₂ by simp only [mul_assoc], d.wittHyperbolic_anisotropic_commute_levi]
    simp only [mul_assoc]
  have hs1 : s 1 1 = 1 := by simp [s]
  have hc := fun a g' => _root_.GlobalTheory.LeviScalar.main D V V' W r C B hs ψ χS χT ω hω χS' χT' ω' hω' μ₀ 𝓨₀ h₀ a g' (s a g')
    (hsC a g') (hsB a g') 1
  choose c hc using hc
  set R := res V V' W C B μ₀ 𝓨₀ with hR
  have dpos := fun a : GL (Fin r) (AE D) => detPow_pos' a W.rank
  have dmul := fun a b : GL (Fin r) (AE D) => detPow_mul' a b W.rank
  have d1 : GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow (1 : GL (Fin r) (AE D)) W.rank = 1 := detPow_one' W.rank
  have dcont : Continuous fun a : GL (Fin r) (AE D) => GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank := continuous_detPow' W.rank

  by_cases hz : ∃ f₀, IsThetaFunO ψ V W f₀ ∧ R f₀ ≠ 0
  swap
  · push_neg at hz
    refine ⟨1, 1, ⟨continuous_const, fun _ => rfl⟩, ⟨continuous_const, fun _ _ => rfl⟩, ?_⟩
    intro μ 𝓨 hμ a g' m _ _ f hf
    rw [hind _ (hω.om_pres _ f hf) μ 𝓨 hμ, hind f hf μ 𝓨 hμ, hz _ (hω.om_pres _ f hf), hz f hf, map_zero,
      smul_zero]
  obtain ⟨f₀, hf₀, hne⟩ := hz
  have hRth : IsThetaFunO ψ V' W (R f₀) := ((GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hω.std μ₀ 𝓨₀ h₀).1 f₀ hf₀).2.1

  have hinj : ∀ (g' : GA D V') (v : WO V' W → ℂ), ω' (g', 1) v = 0 → v = 0 := by
    intro g' v hv
    have : ω' (g'⁻¹, 1) (ω' (g', 1) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one, ← Prod.one_eq_mk, map_one,
        Module.End.one_apply]
    rw [← this, hv, map_zero]
  have huniq : ∀ (g' : GA D V') (k₁ k₂ : ℂ), k₁ • ω' (g', 1) (R f₀) = k₂ • ω' (g', 1) (R f₀) → k₁ = k₂ := by
    intro g' k₁ k₂ h
    have hw : ω' (g', 1) (R f₀) ≠ 0 := fun h0 => hne (hinj g' _ h0)
    exact smul_left_injective ℂ hw h
  let K : GL (Fin r) (AE D) → GA D V' → ℂ := fun a g' => (c a g' : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ)
  have hK : ∀ a g' f, IsThetaFunO ψ V W f → R (ω (s a g', 1) f) = K a g' • ω' (g', 1) (R f) := fun a g' f hf =>
    hc a g' f hf
  have Kmul : ∀ a₁ g₁ a₂ g₂, K (a₁ * a₂) (g₁ * g₂) = K a₁ g₁ * K a₂ g₂ := by
    intro a₁ g₁ a₂ g₂
    apply huniq (g₁ * g₂)
    rw [← hK _ _ f₀ hf₀, hsmul, show ((s a₁ g₁ * s a₂ g₂, (1 : GA D W)) : GA D V × GA D W) = (s a₁ g₁, 1) * (s a₂ g₂, 1) by
      rw [Prod.mk_mul_mk, mul_one], map_mul, Module.End.mul_apply, hK _ _ _ (hω.om_pres _ f₀ hf₀), hK _ _ f₀ hf₀,
      map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have cmul : ∀ a₁ g₁ a₂ g₂, c (a₁ * a₂) (g₁ * g₂) = c a₁ g₁ * c a₂ g₂ := by
    intro a₁ g₁ a₂ g₂
    have h := Kmul a₁ g₁ a₂ g₂
    simp only [K, dmul] at h
    have hd : ((GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a₁ W.rank * GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a₂ W.rank : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (mul_pos (dpos a₁) (dpos a₂)).ne'
    apply Circle.coe_inj.1
    rw [Circle.coe_mul]
    apply mul_right_cancel₀ hd
    rw [h, Complex.ofReal_mul]; ring
  have c11 : c 1 1 = 1 := by
    have h := huniq 1 (K 1 1) 1 (by rw [← hK _ _ f₀ hf₀, hs1, ← Prod.one_eq_mk, ← Prod.one_eq_mk, map_one, map_one, Module.End.one_apply,
      Module.End.one_apply, one_smul])
    simp only [K, d1, Complex.ofReal_one, mul_one] at h
    exact Circle.coe_inj.1 (by rw [h, Circle.coe_one])
  let μa : GL (Fin r) (AE D) →* Circle :=
    { toFun := fun a => c a 1
      map_one' := c11
      map_mul' := fun a b => by rw [← cmul, mul_one] }
  let ξ : GA D V' →* Circle :=
    { toFun := fun g => c 1 g
      map_one' := c11
      map_mul' := fun g g' => by rw [← cmul, mul_one] }
  have csplit : ∀ a g', c a g' = μa a * ξ g' := by
    intro a g'
    have := cmul a 1 1 g'
    rwa [mul_one, one_mul] at this
  refine ⟨μa, ξ, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  ·
    obtain ⟨x₁, hx₁⟩ := Function.ne_iff.1 hne
    have hΦ := _root_.GlobalTheory.ResFirstCont.continuous_res_left D V V' W r C B ψ χS χT ω hω μ₀ 𝓨₀ h₀ f₀ hf₀ x₁
    have heq : ∀ a, ((μa a : Circle) : ℂ) = R (ω (d.levi a, 1) f₀) x₁ /
        ((GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ) * R f₀ x₁) := by
      intro a
      have h := congrFun (hK a 1 f₀ hf₀) x₁
      rw [show s a 1 = d.levi a by simp [s], ← Prod.one_eq_mk, map_one, Module.End.one_apply, Pi.smul_apply,
        smul_eq_mul] at h
      rw [h, eq_div_iff (mul_ne_zero (Complex.ofReal_ne_zero.2 (dpos a).ne') hx₁)]
      simp only [K]; rw [← mul_assoc]; rfl
    refine continuous_induced_rng.2 ?_
    change Continuous fun a => ((μa a : Circle) : ℂ)
    simp only [heq]
    exact (hΦ.comp d.continuous_levi).div ((Complex.continuous_ofReal.comp dcont).mul continuous_const)
      fun a => mul_ne_zero (Complex.ofReal_ne_zero.2 (dpos a).ne') hx₁
  ·
    intro a₀
    have h := huniq 1 (K (Matrix.GeneralLinearGroup.map (incA D) a₀) 1) 1 (by
      rw [← hK _ _ f₀ hf₀, one_smul, ← Prod.one_eq_mk, map_one, Module.End.one_apply,
        show s (Matrix.GeneralLinearGroup.map (incA D) a₀) 1 = d.levi (Matrix.GeneralLinearGroup.map (incA D) a₀) by
          simp [s]]
      exact _root_.GlobalTheory.LeviGLRes.res_levi_GL D V V' W r C B hs d hdC hdB ψ χS χT ω hω μ₀ 𝓨₀ h₀ a₀ f₀ hf₀)
    simp only [K] at h
    have hn := congrArg norm h
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_of_nonneg (dpos _).le, norm_one] at hn
    rw [hn, Complex.ofReal_one, mul_one] at h
    exact Circle.coe_inj.1 (by rw [Circle.coe_one]; exact h)
  ·
    refine continuous_induced_rng.2 ?_
    change Continuous fun g => ((ξ g : Circle) : ℂ)
    rw [continuous_iff_continuousAt]
    intro g₀
    have hw : ω' (g₀, 1) (R f₀) ≠ 0 := fun h0 => hne (hinj g₀ _ h0)
    obtain ⟨x₁, hx₁⟩ := Function.ne_iff.1 hw
    have hΦ := (_root_.GlobalTheory.ResFirstCont.continuous_res_left D V V' W r C B ψ χS χT ω hω μ₀ 𝓨₀ h₀ f₀ hf₀ x₁).comp d.continuous_embed
    have hΨ : Continuous fun g : GA D V' => ω' (g, 1) (R f₀) x₁ :=
      (hω'.om_cont (R f₀) hRth x₁).comp (continuous_id.prodMk continuous_const)
    have heq : ∀ g, ω' (g, 1) (R f₀) x₁ ≠ 0 → ((ξ g : Circle) : ℂ) =
        R (ω (d.emb0 g, 1) f₀) x₁ / ω' (g, 1) (R f₀) x₁ := by
      intro g hg
      have h := congrFun (hK 1 g f₀ hf₀) x₁
      rw [show s 1 g = d.emb0 g by simp [s], Pi.smul_apply, smul_eq_mul] at h
      rw [h, eq_div_iff hg]
      simp only [K, d1, Complex.ofReal_one, mul_one]; rfl
    have hq : ContinuousAt (fun g => R (ω (d.emb0 g, 1) f₀) x₁ / ω' (g, 1) (R f₀) x₁) g₀ :=
      hΦ.continuousAt.div hΨ.continuousAt hx₁
    exact hq.congr ((hΨ.continuousAt.eventually_ne hx₁).mono fun g hg => (heq g hg).symm)
  ·
    intro γ hγ
    have h := huniq γ (K 1 γ) 1 (by
      rw [← hK _ _ f₀ hf₀, one_smul, show s 1 γ = d.emb0 γ by simp [s]]
      exact _root_.GlobalTheory.TowerEmbRat.rational_unitary_acts_on_thetaRestriction_smaller_alt D V V' W r C B hs d hdC hdB ψ χS χT ω hω χS' χT' ω' hω' μ₀ 𝓨₀ h₀ γ hγ f₀ hf₀)
    simp only [K, d1, Complex.ofReal_one, mul_one] at h
    exact Circle.coe_inj.1 (by rw [Circle.coe_one]; exact h)
  ·
    intro μ 𝓨 hμ a g' m h1 h2 f hf
    obtain ⟨n, hn⟩ : ∃ n, n = (s a g')⁻¹ * m := ⟨_, rfl⟩
    have hmn : s a g' * n = m := by rw [hn, mul_inv_cancel_left]
    have hnC : HMul.hMul (mt V n) (C.map (incA D)) = C.map (incA D) := by
      rw [hn, mt_mul, Matrix.mul_assoc, h1, ← hsC a g', ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have hnB : HMul.hMul (mt V n) (B.map (incA D)) = B.map (incA D) := by
      rw [hn, mt_mul, Matrix.mul_assoc, h2, ← hsB a g', ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have hnI : n ∈ NI V C := hker n hnC hnB
    have hnf := hω.om_pres (n, 1) f hf
    have key : ω (m, 1) f = ω (s a g', 1) (ω (n, 1) f) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, hmn]
    have hk : R (ω (n, 1) f) = R f := _root_.GlobalTheory.UnipRes.res_unip D V V' W r C B hs ψ χS χT ω hω μ₀ 𝓨₀ h₀ ⟨n, hnI⟩ f hf
    rw [hind _ (hω.om_pres _ f hf) μ 𝓨 hμ, hind f hf μ 𝓨 hμ, key, hK a g' _ hnf, hk]
    simp only [K, csplit, Circle.coe_mul]
    congr 1
    ring

end GlobalTheory.LeviChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieLatticeOntoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLattice_onto_of_monHom_pair_pow_p_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (I : IntData Xo c T io y.1) (I' : IntData Xo c T io y'.1) (f : Fib Xo (xOf y) ⟶ Fib Xo (xOf y')) (F : I.G.G ⟶ I'.G.G) (F' : I'.G.G ⟶ I.G.G) (p : ℕ) (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), IsUnit (p : T.V) → IsMonHom F → IsMonHom F' → Ext I.m1 I.m2 I'.m1 I'.m2 f F → F ≫ F' = 𝟙 _ ^ (p ^ 2) → F' ≫ F = 𝟙 _ ^ (p ^ 2) → (∀ a, I.G.act.act a ≫ F = F ≫ I'.G.act.act a) → (∀ a, I'.G.act.act a ≫ F' = F' ≫ I.G.act.act a) → letI := io.toAlgebra; (∀ τ j, IsLieImageH p f.left (y.1.u τ j) (v τ j)) → ∃ k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, (∀ τ, IsUnit (k τ).det) ∧ ∀ τ i, IsCombAt y'.1.x (y'.1.u τ) (fun j => algebraMap T.V T.Fr (k τ j i)) (v τ i) := by
  first | exact @GlobalTheory.HkLie.lie_lattice_onto | exact GlobalTheory.HkLie.lie_lattice_onto | (intros; apply GlobalTheory.HkLie.lie_lattice_onto <;> assumption)
end

