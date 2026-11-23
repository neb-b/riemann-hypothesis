module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertUniformisationRiemannForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AnyAppellHumbert

theorem hermForm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm
  rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, h.eq, Matrix.dotProduct_mulVec]

theorem semicharacter_add {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hL : L.IsLB) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (l m : u.Λ) (n : ℤ)
    (hn : (n : ℝ) = (hermForm Hm l m).im) : χ (l + m) = χ l * χ m * (-1) ^ n := by
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex 0).left hL
  have hi' : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [SectionTheta.ex_add_lattice]
  have hi'' : ⊤ ≤ (u.ex (0 + l + m)).left ⁻¹ᵁ L.U i := by rwa [SectionTheta.ex_add_lattice]
  have h1 := h.2.2.2 l i 0 hi
  have h2 := h.2.2.2 m i _ hi'
  have h3 := h.2.2.2 (l + m) i 0 hi
  have hs := hermForm_swap h.1 (l : Fin g → ℂ) m
  have hne := u.fr_ne i _ hi''
  rw [h2, h3] at h1
  simp only [zero_add, Submodule.coe_add, star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    zero_dotProduct, mul_zero] at h1 hne
  unfold hermForm at hs hn
  rw [hs] at h1
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)) = a at h1
  generalize (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = b at h1
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = c at h1 hn
  have hc : c = star c + 2 * n * Complex.I := by
    have := Complex.sub_conj c
    rw [← hn] at this
    push_cast at this
    rw [Complex.star_def]
    linear_combination this
  have he : Complex.exp (Real.pi / 2 * a) * Complex.exp (Real.pi * c + Real.pi / 2 * b) =
      (-1) ^ n * Complex.exp (Real.pi / 2 * (a + star c + (c + b))) := by
    rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination (Real.pi / 2 : ℂ) * hc
  refine mul_right_cancel₀ (mul_ne_zero (Complex.exp_ne_zero (Real.pi / 2 * (a + star c + (c + b)))) hne) ?_
  linear_combination h1 + χ l * χ m * u.fr i (l + m) * he

theorem isAH_properties :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧ (∀ l, χ l = 1 ∨ χ l = -1) ∧ (∀ l m, χ (l + m) = χ l * χ m * (-1) ^ Ef l m) ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧ (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧ ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c) := by
  intro hlaw _ _ hU P u Hm χ hA
  obtain ⟨ht1, ht2, hE⟩ := AnyUnif.tangent_and_unimodular hU P u
  obtain ⟨Ef, hEf, hb⟩ := hE Hm χ hA
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  have hvalext := @eq_of_valAt'_eq hval hvalaff
  have hsmred := @isReduced_of_smooth_complex
  have hholprod := @holFamily_lift hval
  have hthg := @ThetaGroupFrame.thetaGrp_in_frame hval hholprod
  have hweil := @WeilExp.weilIs_exp_riemannForm hlaw.weil hval hvalext hsmred hthg
  have hsecfn := @sections_pow_theta_functions hval hvalext hsmred
  have hfshift := @fourierCoeff_unitCube_translate_of_entire_periodic
  have hfvan := @entire_periodic_eq_zero_of_fourierCoeff_eq_zero hfshift
  have hdimcl := @ClassicalTheta.card_le_pow_of_linearIndependent hfshift hfvan
  have hnormform := @SiegelNormalForm.exists_normal_form
  have hdim := @card_le_pow_of_linearIndependent_theta_principal hnormform hdimcl
  have hindep := @PowSec.exists_indep_sections hlaw.globalSectionsRank
  have hseconto := @ThetaOnto.theta_from_section hval hdim hindep hsecfn
  have h7 := hsecfn P u Hm χ Ef ⟨hA.1, hA.2.2.1, hEf, hA.2.2.2⟩
  refine ⟨Ef, hEf, hb, fun l => sq_eq_one_iff.1 (semicharacter_sq_eq_one_of_symmetric P u Hm χ hA l), fun l m => semicharacter_add P.isLB u hA l m _ (hEf l m),
    ht1, ht2, fun n => ⟨(h7 n).1, fun θ hθ => ?_⟩, hweil P u Hm χ Ef ⟨hA.1, hA.2.2.1, hEf, hA.2.2.2⟩⟩
  obtain ⟨s, hs⟩ := hseconto P u Hm χ Ef hA ⟨hA.1, hA.2.2.1, hEf, hA.2.2.2⟩ hb n θ hθ
  exact ⟨s, hs, fun s' hs' => (h7 n).2 θ s' s hs' hs⟩

end GlobalTheory.AnyAppellHumbert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionOfDiagonalCMAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.detCond_of_diagonal_action : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (ty : Fin P.g → (E →+* ℂ)), u.IsAH Hm χ → IsTypeFn H D.p D.q ty → (∀ (a : 𝓞 E) z, u.ex (fun i => ty i (a : E) * z i) = u.ex z ≫ act.act a) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : ℂ →+* K), DetCond D act (spMap β) (β H.rt0) := by
  intro _ _ _ unif E _ _ _ H D P u _ _ act ty _ hty hact K _ _ β
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.AnyUnif.tangent_and_unimodular unif P u
  have hs : Smooth P.A.hom := P.isAb.smooth
  obtain ⟨v, hv, heig⟩ := GlobalTheory.exists_lieBasis_of_holUnif P.A P.L P.g u hs h₁ h₂
  have key : ∀ τ₀ : E →+* ℂ, LieMult act (𝟙 (Sp ℂ)) (τ₀.comp (algebraMap (𝓞 E) E))
      (Nat.card {i // ty i = τ₀}) := fun τ₀ => by
    have h := GlobalTheory.lieMult_of_eigenbasis ℂ (𝓞 E) P.A act P.g v (fun i => (ty i).comp (algebraMap (𝓞 E) E)) hs hv
      (fun i a => heig _ _ (act.hom a) (hact a) i) (τ₀.comp (algebraMap (𝓞 E) E))
    convert h using 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun i =>
      ⟨fun e => by rw [e], fun e => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e⟩)
  have hd : DetCond D act (𝟙 (Sp ℂ)) H.rt0 := fun τ => by
    obtain ⟨τ₀, rfl⟩ := GlobalTheory.PeriodPoint.exists_embedding (RingHom.id ℂ) τ
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← (hty τ₀).1 h]; exact key τ₀
    · rw [← (hty τ₀).2 h]; exact key τ₀
  have := (GlobalTheory.detCond_iff_of_field_extension E H D _ P.A ℂ K β (𝟙 _) act H.rt0 hs).2 hd
  rwa [Category.comp_id] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfBiadditiveSliceTrivialEighthPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_biadditive_slice_trivial_eighthPower : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.KTriv G L → ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  first | exact @GlobalTheory.FormBundleKer.eq_one_of_slice_trivial | exact GlobalTheory.FormBundleKer.eq_one_of_slice_trivial | (intros; apply GlobalTheory.FormBundleKer.eq_one_of_slice_trivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreFrameOfMemClosure
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open scoped Topology
open Filter

namespace GlobalTheory.ThetaFamily

variable {g m : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : RigLB G}

def IsFibreFrame (L : RigLB G) (y : Sp ℂ ⟶ S) (e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)) (θ : (Fin g → ℂ) → ℂ)
    (fr : L.L.ι → (Fin g → ℂ) → ℂ) : Prop :=
  (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.L.U j}) ∧
  (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.L.U j → fr j z ≠ 0) ∧
  (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.L.U j ⊓ L.L.U j') →
    fr j z = valAt' (e z) (L.L.U j ⊓ L.L.U j') (L.L.g j j').val * fr j' z) ∧
  (∀ j, ⊤ ≤ e 0 ⁻¹ᵁ L.L.U j →
    fr j 0 = valAt' y ((L.L.pull (eSec G)).U (fun _ => j)) (L.rig.s (fun _ => j)).val) ∧
  ∃ s : (L.L.pull (pullback.fst G.hom y)).Sec, ∀ j z (x : Sp ℂ ⟶ pullback G.hom y),
    x ≫ pullback.fst _ _ = e z → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ e z ⁻¹ᵁ L.L.U j →
    valAt' x ((L.L.pull (pullback.fst G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z

def SpansFibre (L : RigLB G) (y : Sp ℂ ⟶ S) (V : S.Opens) (θ₀ : ∀ j, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.L.U j)) : Prop :=
  ∀ σ : LB.Sec (L.L.pull (pullback.fst G.hom y)), ∃ a : ℂ, ∀ j (x : Sp ℂ ⟶ pullback G.hom y),
    x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (x ≫ pullback.fst _ _) ⁻¹ᵁ L.L.U j →
    valAt' x ((L.L.pull (pullback.fst G.hom y)).U (fun _ => j)) (σ.f (fun _ => j)) =
      a * valAt' (x ≫ pullback.fst _ _) (G.hom ⁻¹ᵁ V ⊓ L.L.U j) (θ₀ j)

theorem isThetaFrame_singleton_iff {y : (Fin m → ℂ) → (Sp ℂ ⟶ S)}
    {e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} {θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ} {b : Fin m → ℂ} :
    IsThetaFrame L {b} y e θ ↔ ∃ fr, IsFibreFrame L (y b) (e b) (θ b) fr := by
  constructor
  · rintro ⟨fr, h1, h2, h3, h4, h5⟩
    exact ⟨fun j z => fr j (b, z), fun j => (h1 j).comp (f := fun z => (b, z)) (by fun_prop) fun z hz => ⟨rfl, hz⟩,
      fun j z => h2 j b z rfl, fun j j' z => h3 j j' b z rfl, fun j => h4 j b rfl, h5 b rfl⟩
  · rintro ⟨fr, h1, h2, h3, h4, h5⟩
    refine ⟨fun j bz => fr j bz.2, fun j => (h1 j).comp (f := Prod.snd) (by fun_prop) ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨_, z⟩ ⟨rfl, hz⟩; exact hz
    · rintro j _ z rfl; exact h2 j z
    · rintro j j' _ z rfl; exact h3 j j' z
    · rintro j _ rfl; exact h4 j
    · rintro _ rfl; exact h5

section Fibre

variable {y : Sp ℂ ⟶ S} {e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} {θ θ' : (Fin g → ℂ) → ℂ} {fr : L.L.ι → (Fin g → ℂ) → ℂ}

theorem exists_chart_point (L : RigLB G) (x : Sp ℂ ⟶ G.left) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.L.U j := by
  obtain ⟨j, hj⟩ := exists_chart L.isLB (x (default : PrimeSpectrum ℂ))
  exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩

theorem IsFibreFrame.rescale (h : IsFibreFrame L y e θ fr) {ρ : (Fin g → ℂ) → ℂ} (hd : Differentiable ℂ ρ)
    (h0 : ∀ z, ρ z ≠ 0) (hρ : ∀ z, ρ z * θ z = θ' z) :
    IsFibreFrame L y e θ' (fun j z => fr j z * (ρ 0 * (ρ z)⁻¹)) := by
  obtain ⟨h1, h2, h3, h4, s, h5⟩ := h
  refine ⟨fun j => (h1 j).mul ((differentiable_const _).mul (hd.inv h0)).differentiableOn,
    fun j z hz => mul_ne_zero (h2 j z hz) (mul_ne_zero (h0 _) (inv_ne_zero (h0 _))),
    fun j j' z hz => by simp only [h3 j j' z hz, _root_.mul_assoc],
    fun j hj => by simp only [mul_inv_cancel₀ (h0 0), _root_.mul_one, h4 j hj], ?_⟩
  obtain ⟨t, ht⟩ := exists_sec_const_mul (pullback.snd G.hom y) s (ρ 0)
  refine ⟨t, fun j z x x1 x2 hz => ?_⟩
  have hz' : ⊤ ≤ (x ≫ pullback.fst G.hom y) ⁻¹ᵁ L.L.U j := by rw [x1]; exact hz
  rw [ht (fun _ => j) x x2 (fun p hp => mem_pull.2 (hz' hp)), h5 j z x x1 x2 hz, ← hρ]
  have := h0 z
  field_simp

theorem IsFibreFrame.ratio (h : IsFibreFrame L y e θ fr) (he : ∀ z, e z ≫ G.hom = y) (hθ : θ ≠ 0) {V : S.Opens}
    {θ₀ : ∀ j, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.L.U j)} (hV : SpansFibre L y V θ₀) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.L.U j →
      fr j z * a⁻¹ * θ z = valAt' (e z) (G.hom ⁻¹ᵁ V ⊓ L.L.U j) (θ₀ j) := by
  obtain ⟨-, h2, -, -, s, hs⟩ := h
  obtain ⟨a, ha⟩ := hV s
  have key : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.L.U j → θ z * fr j z = a * valAt' (e z) (G.hom ⁻¹ᵁ V ⊓ L.L.U j) (θ₀ j) := by
    intro j z hz
    let x : Sp ℂ ⟶ pullback G.hom y := pullback.lift (e z) (𝟙 _) ((he z).trans (Category.id_comp _).symm)
    have h₁ : x ≫ pullback.fst _ _ = e z := pullback.lift_fst _ _ _
    have h₂ : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    rw [← hs j z x h₁ h₂ hz, ha j x h₂ (by rw [h₁]; exact hz), h₁]
  have a0 : a ≠ 0 := fun h0 => hθ (funext fun z => by
    obtain ⟨j, hj⟩ := exists_chart_point L (e z)
    have e := key j z hj
    rw [h0, zero_mul] at e
    exact (mul_eq_zero.1 e).resolve_right (h2 j z hj))
  refine ⟨a, a0, fun j z hz => ?_⟩
  rw [mul_right_comm, mul_comm (fr j z), key j z hz]
  field_simp

end Fibre

section Family

variable {B : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ S)} {e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}
  {θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ}

theorem mem_chart_iff {x : Sp ℂ ⟶ G.left} {u : Sp ℂ ⟶ S} (h : x ≫ G.hom = u) (V : S.Opens) (U : G.left.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (G.hom ⁻¹ᵁ V ⊓ U) ↔ ⊤ ≤ u ⁻¹ᵁ V ∧ ⊤ ≤ x ⁻¹ᵁ U := by
  rw [top_le_preimage_inf, ← top_le_preimage_comp, h]

theorem exists_fibreFrame_of_mem_closure (he : ∀ b ∈ B, ∀ z, e b z ≫ G.hom = y b)
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2))
    (hd : DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => θ bz.1 bz.2) (B ×ˢ Set.univ))
    (hnz : ∀ b ∈ B, ∀ z, ∃ᶠ w in 𝓝 z, θ b w ≠ 0) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) {V : S.Opens}
    {θ₀ : ∀ j, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.L.U j)} (hV₀ : ⊤ ≤ y b₀ ⁻¹ᵁ V)
    (hV : ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ V → SpansFibre L (y b) V θ₀)
    {T : Set (Fin m → ℂ)} (hT : ∀ b ∈ T, ∃ fr, IsFibreFrame L (y b) (e b) (θ b) fr) (hcl : b₀ ∈ closure T)
    {θ' : (Fin g → ℂ) → ℂ} (hnz' : ∀ z, ∃ᶠ w in 𝓝 z, θ' w ≠ 0) {fr' : L.L.ι → (Fin g → ℂ) → ℂ}
    (h' : IsFibreFrame L (y b₀) (e b₀) θ' fr') : ∃ fr, IsFibreFrame L (y b₀) (e b₀) (θ b₀) fr := by
  have ne : ∀ {f : (Fin g → ℂ) → ℂ}, (∀ z, ∃ᶠ w in 𝓝 z, f w ≠ 0) → f ≠ 0 := fun h h0 =>
    (h 0).exists.elim fun w hw => hw (congrFun h0 w)
  obtain ⟨a', ha', hr'⟩ := h'.ratio (he b₀ hb₀) (ne hnz') (hV b₀ hb₀ hV₀)
  suffices hloc : ∀ z, ∃ ρ : (Fin g → ℂ) → ℂ, ρ z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧ ρ w * θ' w = θ b₀ w by
    obtain ⟨ρ, h1, h2, h3⟩ := exists_entire_quotient hnz' hloc
    exact ⟨_, h'.rescale h1 h2 h3⟩
  intro z₀
  obtain ⟨j, hj⟩ := exists_chart_point L (e b₀ z₀)
  obtain ⟨hW, hf⟩ := hol (G.hom ⁻¹ᵁ V ⊓ L.L.U j) (θ₀ j)
  set W := {bz ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e bz.1 bz.2 ⁻¹ᵁ (G.hom ⁻¹ᵁ V ⊓ L.L.U j)} with hWd
  have mW : ∀ b z, (b, z) ∈ W → b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ V ∧ ⊤ ≤ e b z ⁻¹ᵁ L.L.U j := fun b z h =>
    ⟨h.1.1, (mem_chart_iff (he b h.1.1 z) _ _).1 h.2⟩
  have hw : (b₀, z₀) ∈ W := ⟨⟨hb₀, trivial⟩, (mem_chart_iff (he b₀ hb₀ z₀) _ _).2 ⟨hV₀, hj⟩⟩
  have hθW := hd.mono (fun bz h => h.1 : W ⊆ B ×ˢ Set.univ)
  have hS : ∀ b ∈ T, ∃ F : (Fin g → ℂ) → ℂ, DifferentiableOn ℂ F {z | (b, z) ∈ W} ∧ ∀ z, (b, z) ∈ W →
      F z ≠ 0 ∧ F z * θ b z = valAt' (e b z) (G.hom ⁻¹ᵁ V ⊓ L.L.U j) (θ₀ j) := by
    intro b hb
    by_cases hm : b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ V
    · obtain ⟨fr, h⟩ := hT b hb
      obtain ⟨a, ha, hr⟩ := h.ratio (he b hm.1) (ne (hnz b hm.1)) (hV b hm.1 hm.2)
      exact ⟨fun z => fr j z * a⁻¹, ((h.1 j).mono fun z hz => (mW b z hz).2.2).mul_const _, fun z hz =>
        ⟨mul_ne_zero (h.2.1 j z (mW b z hz).2.2) (inv_ne_zero ha), hr j z (mW b z hz).2.2⟩⟩
    · exact ⟨0, differentiableOn_const _, fun z hz => absurd ⟨(mW b z hz).1, (mW b z hz).2.1⟩ hm⟩
  have hc : Continuous fun z : Fin g → ℂ => (b₀, z) := by fun_prop
  have hWz : ∀ᶠ z in 𝓝 z₀, (b₀, z) ∈ W := hc.continuousAt.eventually (hW.mem_nhds hw)
  obtain ⟨U₁, G₁, o₁, w₁, -, d₁, q₁⟩ := exists_quotient_closure hW hf hθW (S := T)
    (fun b hb => (hS b hb).imp fun F h => ⟨h.1, fun z hz => (h.2 z hz).2⟩) hw (hnz b₀ hb₀ z₀)
  obtain ⟨U₂, G₂, o₂, w₂, -, d₂, q₂⟩ := exists_quotient_closure hW hθW hf (S := T)
    (fun b hb => (hS b hb).elim fun F h => ⟨fun z => (F z)⁻¹, h.1.inv fun z hz => (h.2 z hz).1, fun z hz => by
      rw [← (h.2 z hz).2, inv_mul_cancel_left₀ (h.2 z hz).1]⟩) hw
    (((hnz' z₀).and_eventually hWz).mono fun z hz => by
      have := (mW _ _ hz.2).2.2
      rw [← hr' j z this]
      exact mul_ne_zero (mul_ne_zero (h'.2.1 j z this) (inv_ne_zero ha')) hz.1)
  have e₁ : ∀ᶠ z in 𝓝 z₀, (b₀, z) ∈ U₁ := hc.continuousAt.eventually (o₁.mem_nhds w₁)
  have e₂ : ∀ᶠ z in 𝓝 z₀, (b₀, z) ∈ U₂ := hc.continuousAt.eventually (o₂.mem_nhds w₂)
  have hι : Differentiable ℂ fun z : Fin g → ℂ => (b₀, z) := by fun_prop
  have s₁ : DifferentiableAt ℂ (fun z => G₁ (b₀, z)) z₀ := (d₁.differentiableAt (o₁.mem_nhds w₁)).comp z₀ (hι z₀)
  have s₂ : ∀ z, (b₀, z) ∈ U₂ → DifferentiableAt ℂ (fun z => G₂ (b₀, z)) z := fun z hz =>
    (d₂.differentiableAt (o₂.mem_nhds hz)).comp z (hι z)
  have one : G₂ (b₀, z₀) * G₁ (b₀, z₀) = 1 := by
    refine tendsto_nhds_unique_of_frequently_eq ((s₂ z₀ w₂).mul s₁).continuousAt tendsto_const_nhds
      (((hnz b₀ hb₀ z₀).and_eventually (e₁.and e₂)).mono fun z hz => mul_right_cancel₀ hz.1 ?_)
    have p₁ := q₁ _ hz.2.1 hcl
    have p₂ := q₂ _ hz.2.2 hcl
    simp only [Pi.mul_apply] at p₁ p₂ ⊢
    rw [_root_.mul_assoc, p₁, p₂, _root_.one_mul]
  refine ⟨fun z => G₂ (b₀, z) * (fr' j z * a'⁻¹),
    mul_ne_zero (left_ne_zero_of_mul_eq_one one) (mul_ne_zero (h'.2.1 j z₀ hj) (inv_ne_zero ha')), ?_⟩
  filter_upwards [e₂, hWz.eventually_nhds] with z hz hz'
  refine ⟨(s₂ z hz).mul (((h'.1 j).differentiableAt (hz'.mono fun w hw => (mW _ _ hw).2.2)).mul_const _), ?_⟩
  rw [_root_.mul_assoc, hr' j z (mW _ _ hz'.self_of_nhds).2.2]
  exact q₂ _ hz hcl

theorem isThetaFrame_of_fibreFrames (he : ∀ b ∈ B, ∀ z, e b z ≫ G.hom = y b) (he0 : ∀ b ∈ B, e b 0 = y b ≫ eSec G)
    (holy : IsHolTo B y) (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2))
    (hd : DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => θ bz.1 bz.2) (B ×ˢ Set.univ))
    (hnz : ∀ b ∈ B, ∀ z, ∃ᶠ w in 𝓝 z, θ b w ≠ 0)
    (hsec : ∀ b₀ ∈ B, ∃ (V : S.Opens) (θ₀ : ∀ j, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.L.U j)), ⊤ ≤ y b₀ ⁻¹ᵁ V ∧
      ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ V → SpansFibre L (y b) V θ₀)
    (hT : ∀ b ∈ B, ∃ fr, IsFibreFrame L (y b) (e b) (θ b) fr) : IsThetaFrame L B y e θ := by
  choose! fr hfr using hT
  refine ⟨fun j bz => fr bz.1 j bz.2, fun j w hw => ?_, fun j b z hb => (hfr b hb).2.1 j z,
    fun j j' b z hb => (hfr b hb).2.2.1 j j' z, fun j b hb => (hfr b hb).2.2.2.1 j, fun b hb => (hfr b hb).2.2.2.2⟩
  obtain ⟨b₀, z₀⟩ := w
  obtain ⟨hb₀, hj⟩ : b₀ ∈ B ∧ ⊤ ≤ e b₀ z₀ ⁻¹ᵁ L.L.U j := hw
  obtain ⟨V, θ₀, hV₀, hV⟩ := hsec b₀ hb₀
  have ex : ∀ b, b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ V → ∃ a : ℂ, a ≠ 0 ∧ ∀ j z, ⊤ ≤ e b z ⁻¹ᵁ L.L.U j →
      fr b j z * a⁻¹ * θ b z = valAt' (e b z) (G.hom ⁻¹ᵁ V ⊓ L.L.U j) (θ₀ j) := fun b hb =>
    (hfr b hb.1).ratio (he b hb.1) (fun h0 => (hnz b hb.1 0).exists.elim fun w hw => hw (congrFun h0 w)) (hV b hb.1 hb.2)
  choose! a ha hr using ex
  have hF : ∀ k z, ⊤ ≤ e b₀ z ⁻¹ᵁ L.L.U k →
      DifferentiableAt ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => fr bz.1 k bz.2 * (a bz.1)⁻¹) (b₀, z) := by
    intro k z hk
    obtain ⟨hW, hf⟩ := hol (G.hom ⁻¹ᵁ V ⊓ L.L.U k) (θ₀ k)
    set W := {bz ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e bz.1 bz.2 ⁻¹ᵁ (G.hom ⁻¹ᵁ V ⊓ L.L.U k)} with hWd
    have mW : ∀ b z, (b, z) ∈ W → (b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ V) ∧ ⊤ ≤ e b z ⁻¹ᵁ L.L.U k := fun b z h =>
      and_assoc.2 ⟨h.1.1, (mem_chart_iff (he b h.1.1 z) _ _).1 h.2⟩
    have hw : (b₀, z) ∈ W := ⟨⟨hb₀, trivial⟩, (mem_chart_iff (he b₀ hb₀ z) _ _).2 ⟨hV₀, hk⟩⟩
    refine (differentiableOn_quotient_of_differentiableOn_slice _ _ W _ _ _ hW hf (hd.mono fun bz h => h.1)
      (fun w hw => hr _ (mW _ _ hw).1 k _ (mW _ _ hw).2) (fun b => ?_)
      (fun w hw => hnz _ hw.1.1 _)).differentiableAt (hW.mem_nhds hw)
    by_cases hb : b ∈ B
    · exact (((hfr b hb).1 k).mono fun z hz => (mW b z hz).2).mul_const (a b)⁻¹
    · exact fun z hz => absurd hz.1.1 hb
  obtain ⟨k, hk⟩ := exists_chart_point L (e b₀ 0)
  obtain ⟨hO, hρ⟩ := holy ((L.L.pull (eSec G)).U (fun _ => k)) (L.rig.s (fun _ => k)).val
  have mO : ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ ((L.L.pull (eSec G)).U (fun _ => k)) ↔ ⊤ ≤ e b 0 ⁻¹ᵁ L.L.U k := fun b hb => by
    rw [he0 b hb, top_le_preimage_iff_mem, top_le_preimage_iff_mem]
    exact mem_pull
  have nO := hO.mem_nhds (⟨hb₀, (mO b₀ hb₀).2 hk⟩ : b₀ ∈ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ ((L.L.pull (eSec G)).U (fun _ => k))})
  have nV := (holy V 0).1.mem_nhds (⟨hb₀, hV₀⟩ : b₀ ∈ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ V})
  have hι : Differentiable ℂ fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ)) := by fun_prop
  have d0 : DifferentiableAt ℂ (fun b => fr b k 0 * (a b)⁻¹) b₀ :=
    DifferentiableAt.comp (f := fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ))) b₀ (hF k 0 hk) (hι b₀)
  have da : DifferentiableAt ℂ a b₀ := by
    refine ((hρ.differentiableAt nO).mul (d0.inv (mul_ne_zero ((hfr b₀ hb₀).2.1 k 0 hk)
      (inv_ne_zero (ha b₀ ⟨hb₀, hV₀⟩))))).congr_of_eventuallyEq ?_
    filter_upwards [nO, nV] with b h1 h2
    have h3 := (mO b h1.1).1 h1.2
    have h4 := (hfr b h1.1).2.1 k 0 h3
    have h5 := ha b h2
    refine Eq.trans ?_ (congrArg (· * (fr b k 0 * (a b)⁻¹)⁻¹) ((hfr b h1.1).2.2.2.1 k h3))
    field_simp
  refine (((hF j z₀ hj).mul (da.comp (b₀, z₀) differentiableAt_fst)).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [(continuous_fst.continuousAt (x := (b₀, z₀))).preimage_mem_nhds nV] with bz h
  exact (inv_mul_cancel_right₀ (ha _ h) _).symm

end Family

end GlobalTheory.ThetaFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsConstKOfLocDerK
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_isConstK_of_locDerK :
    Out.Laws → ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (R : Type) [CommRing R] (xD : R →+* DualNumber K) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ψ : A'.left ⟶ A.left) (j : A₀.left ⟶ A'.left) (d : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, (j ≫ ψ) ⁻¹ᵁ W)), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) ψ → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j → LocDerK A₀.hom A.hom (j ≫ ψ) (fun r => (xD r).snd) ⊤ d → ∃ ρ, IsConstK A' A₀ ρ j := by
  intro hL K _ A₀ _ R _ xD A _ A' _ ψ j d hA₀ hA' hψ hj hd

  have hra : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 (Sp K) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of K)
    ext x
    simp
  have : Flat A₀.hom := inferInstance

  have hρ : IsPullback (pullback.fst A₀.hom (spMap (algebraMap K (DualNumber K)))) (pullback.snd _ _)
      A₀.hom (spMap (algebraMap K (DualNumber K))) := IsPullback.of_hasPullback _ _
  obtain ⟨j₀, hj₀ρ, hj₀π⟩ : ∃ j₀ : A₀.left ⟶ pullback A₀.hom (spMap (algebraMap K (DualNumber K))),
      j₀ ≫ pullback.fst _ _ = 𝟙 _ ∧
        j₀ ≫ pullback.snd _ _ = A₀.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom :=
    ⟨pullback.lift (𝟙 _) (A₀.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
      (by rw [Category.assoc, hra, Category.comp_id, Category.id_comp]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hj₀ : IsPullback j₀ A₀.hom (pullback.snd A₀.hom (spMap (algebraMap K (DualNumber K))))
      (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    refine IsPullback.of_right ?_ hj₀π hρ
    rw [hj₀ρ, hra]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

  have hm : (j ≫ ψ) ≫ A.hom = A₀.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap xD := by
    rw [Category.assoc, hψ.1.w, ← Category.assoc, hj.1.w, Category.assoc]
  obtain ⟨Φ, hΦj, hΦp, -⟩ := DerMorK.exists_hom_of_derivation K A₀.left _ A₀.hom (pullback.snd _ _)
    (pullback.fst _ _) j₀ hρ hj₀ρ hj₀π R xD A.left A.hom (j ≫ ψ) d hm hd

  obtain ⟨e, heψ, heh⟩ : ∃ e : pullback A₀.hom (spMap (algebraMap K (DualNumber K))) ⟶ A'.left,
      e ≫ ψ = Φ ∧ e ≫ A'.hom = pullback.snd _ _ :=
    ⟨hψ.1.lift Φ _ hΦp, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  have hje : j₀ ≫ e = j := by
    apply hψ.1.hom_ext
    · rw [Category.assoc, heψ, hΦj]
    · rw [Category.assoc, heh, hj₀π, hj.1.w]

  have : IsIso e := _root_.GlobalTheory.isIso_of_id_mod_eps K A₀.left _ A'.left A₀.hom (pullback.snd _ _) A'.hom j₀ j e hj₀ hj.1
    inferInstance heh hje
  refine exists_isConstK_of_isPullback hL K A₀ A' (inv e ≫ pullback.fst _ _) j hA₀ hA' hj ?_ ?_
  · have h1 : IsPullback (inv e) A'.hom (pullback.snd A₀.hom (spMap (algebraMap K (DualNumber K)))) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsIso.inv_comp_eq, heh]⟩
    have h2 := h1.paste_horiz hρ
    rwa [Category.id_comp] at h2
  · rw [← hje, Category.assoc, IsIso.hom_inv_id_assoc, hj₀ρ]

end GlobalTheory.KS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsOActOfMapLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

private theorem isMonHom_mul_of_isCommMonObj {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) := by
  rw [Hom.mul_def]
  infer_instance

theorem exists_oAct_of_map_lattice :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (O : Type) [CommRing O] (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (r : O →+* Module.End ℂ (Fin P.g → ℂ)), (∀ a, ∀ z ∈ u.Λ, r a z ∈ u.Λ) → ∃ act : OAct O P.A, ∀ a z, u.ex (r a z) = u.ex z ≫ act.act a := by
  intro hL hL2 hGen hTh O _ P u r hr

  have key : ∀ a, ∃! f : P.A ⟶ P.A, IsMonHom f ∧ ∀ z, u.ex (r a z) = u.ex z ≫ f := fun a =>
    existsUnique_isMonHom_of_map_lattice hL hL2 hGen hTh P P P.L P.L u u (r a) (hr a)
  choose act hact huniq using key
  have eq_of : ∀ a (h : P.A ⟶ P.A), IsMonHom h → (∀ z, u.ex (r a z) = u.ex z ≫ h) → h = act a :=
    fun a h h1 h2 => huniq a h ⟨h1, h2⟩
  have hom : ∀ a, IsMonHom (act a) := fun a => (hact a).1
  refine ⟨⟨act, hom, ?_, ?_, ?_⟩, fun a z => (hact a).2 z⟩
  · refine (eq_of 1 (𝟙 _) inferInstance ?_).symm
    intro z
    simp
  · intro a b
    refine (eq_of (a * b) (act a ≫ act b) inferInstance ?_).symm
    intro z
    rw [mul_comm a b, map_mul, mul_apply_eq_comp, (hact b).2, (hact a).2, Category.assoc]
  · intro a b
    have := hom a
    have := hom b
    refine (eq_of (a + b) (act a * act b) (isMonHom_mul_of_isCommMonObj _ _) ?_).symm
    intro z

    rw [map_add (f := _), LinearMap.add_apply, u.2, (hact a).2, (hact b).2, MonObj.comp_mul]

end GlobalTheory
end

