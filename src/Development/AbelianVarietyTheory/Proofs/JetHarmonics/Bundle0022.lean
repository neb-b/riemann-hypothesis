module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsImEqLattice
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorsionLiftPairingInOrthogonalFrame

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RingHomPointBijective
section
open PowerSeries GlobalTheory.MomOne WeierstrassCurve WeierstrassCurve.Affine
open scoped ComplexConjugate BigOperators Topology
open Classical

noncomputable section

namespace GlobalTheory.MomOne

def ringHomPointFun {k k' : Type*} [Field k] [Field k'] (f : k →+* k') (W : WeierstrassCurve k) :
    W.toAffine.Point → (W.map f).toAffine.Point
  | .zero => 0
  | .some x y hP => .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr hP)

def ringHomPoint {k k' : Type*} [Field k] [Field k'] (f : k →+* k') (W : WeierstrassCurve k) :
    W.toAffine.Point →+ (W.map f).toAffine.Point :=
  AddMonoidHom.mk' (ringHomPointFun f W) <| by
    refine GlobalTheory.map_add_of_triples _ rfl ?_ ?_
    · rintro (_ | ⟨x, y, hP⟩)
      · rfl
      · simp only [Point.neg_some, ringHomPointFun, Point.some.injEq, true_and, negY,
          map_a₁, map_a₃, map_sub, map_neg, map_mul]
    · rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) (_ | ⟨x₃, y₃, h₃⟩) hP hQ hR h
      any_goals first | exact absurd rfl hP | exact absurd rfl hQ | exact absurd rfl hR
      obtain ⟨l, n, e₁, e₂, e₃, s₁, s₂, -⟩ := GlobalTheory.exists_line_of_add_add_eq_zero h
      refine GlobalTheory.add_add_eq_zero_of_line _ _ _ (f l) (f n) ?_ ?_ ?_ ?_ ?_
      · rw [e₁]; simp
      · rw [e₂]; simp
      · rw [e₃]; simp
      · simpa using congrArg f s₁
      · simpa [map_ofNat] using congrArg f s₂

open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
private lemma ringHomPoint_some {k k' : Type*} [Field k] [Field k']
    (f : k →+* k') (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Nonsingular x y) :
    _root_.GlobalTheory.MomOne.ringHomPoint f W (.some x y h) =
      .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr h) := rfl

open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
private lemma ringHomPoint_surjective_of_ringEquiv {k k' : Type*} [Field k] [Field k']
    (e : k ≃+* k') (W : WeierstrassCurve k) :
    Function.Surjective (_root_.GlobalTheory.MomOne.ringHomPoint (e : k →+* k') W) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, map_zero _⟩
  · have h' : W.toAffine.Nonsingular (e.symm x) (e.symm y) := by
      rw [← WeierstrassCurve.Affine.map_nonsingular W.toAffine (f := (e : k →+* k')) e.injective]
      simpa using h
    refine ⟨.some _ _ h', ?_⟩
    rw [ringHomPoint_some]
    simp

open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
private lemma ringHomPoint_eq_zero_iff {k k' : Type*} [Field k] [Field k']
    (f : k →+* k') (W : WeierstrassCurve k) (P : W.toAffine.Point) :
    _root_.GlobalTheory.MomOne.ringHomPoint f W P = 0 ↔ P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rw [ringHomPoint_some]
    simp


open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
theorem _root_.GlobalTheory.MomOne.Mdl.exists_pointHom (q : ℕ) [Fact q.Prime]
    (M : _root_.GlobalTheory.MomOne.Mdl q) (hM : M.Ok) :
    ∃ φ : ℂ →+ M.W.toAffine.Point, Function.Surjective φ ∧
      (∀ z, φ z = 0 ↔ z ∈ M.L.lattice) ∧
      ∀ z ∉ M.L.lattice, ∃ h,
        φ z = WeierstrassCurve.Affine.Point.some (M.ι (M.x z))
          (M.ι (M.y z)) h := by
  obtain ⟨hc, -, -, -, -, -, -, h₄, h₆⟩ := hM
  have hιc : M.ι M.c ≠ 0 :=
    (map_ne_zero M.ι).mpr hc
  obtain ⟨C, hCu, hCr, hCs, hCt⟩ : ∃ C : VariableChange ℂ_[q],
      (C.u : ℂ_[q]) = (M.ι M.c)⁻¹ ∧
      C.r = -(M.W.b₂ / 12) ∧ C.s = -(M.W.a₁ / 2) ∧
      C.t = M.W.a₁ * M.W.b₂ / 24 -
        M.W.a₃ / 2 :=
    ⟨⟨Units.mk0 _ (inv_ne_zero hιc), _, _, _⟩, rfl, rfl, rfl, rfl⟩
  have hCu' : ((C.u⁻¹ : ℂ_[q]ˣ) : ℂ_[q]) = M.ι M.c := by
    rw [Units.val_inv_eq_inv_val, hCu, inv_inv]
  have hE : (_root_.GlobalTheory.latticeCurve M.L).a₁ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₂ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₃ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₄ = -M.L.g₂ / 4 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₆ = -M.L.g₃ / 4 := by
    simp [_root_.GlobalTheory.latticeCurve]
  obtain ⟨hE₁, hE₂, hE₃, hE₄, hE₆⟩ := hE
  have hg₂ : M.ι M.L.g₂ =
      M.W.c₄ / 12 * M.ι M.c ^ 4 := by
    rw [h₄, map_div₀, map_pow, div_mul_cancel₀ _ (pow_ne_zero 4 hιc)]
  have hg₃ : M.ι M.L.g₃ =
      M.W.c₆ / 216 * M.ι M.c ^ 6 := by
    rw [h₆, map_div₀, map_pow, div_mul_cancel₀ _ (pow_ne_zero 6 hιc)]
  have hC : C • M.W =
      (_root_.GlobalTheory.latticeCurve M.L).map (M.ι : ℂ →+* ℂ_[q]) := by
    ext
    · rw [variableChange_a₁, hCu', hCs, map_a₁, hE₁]; simp only [map_zero]; ring
    · rw [variableChange_a₂, hCu', hCs, hCr, map_a₂, hE₂]
      simp only [map_zero, WeierstrassCurve.b₂]; ring
    · rw [variableChange_a₃, hCu', hCt, hCr, map_a₃, hE₃]
      simp only [map_zero, WeierstrassCurve.b₂]; ring
    · rw [variableChange_a₄, hCu', hCs, hCt, hCr, map_a₄, hE₄]
      simp only [RingHom.coe_coe, map_div₀, map_neg, map_ofNat, hg₂, WeierstrassCurve.c₄,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      ring
    · rw [variableChange_a₆, hCu', hCt, hCr, map_a₆, hE₆]
      simp only [RingHom.coe_coe, map_div₀, map_neg, map_ofNat, hg₃, WeierstrassCurve.c₆,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      ring
  let φ : ℂ →+ M.W.toAffine.Point :=
    (_root_.GlobalTheory.variableChangePoint C hC).comp
      ((_root_.GlobalTheory.MomOne.ringHomPoint (M.ι : ℂ →+* ℂ_[q])
        (_root_.GlobalTheory.latticeCurve M.L)).comp
        (_root_.GlobalTheory.latticePointHom M.L))
  have hφ : ∀ z, φ z = _root_.GlobalTheory.variableChangePoint C hC
      (_root_.GlobalTheory.MomOne.ringHomPoint (M.ι : ℂ →+* ℂ_[q])
        (_root_.GlobalTheory.latticeCurve M.L)
        (_root_.GlobalTheory.latticePoint M.L z)) := by
    intro z
    simp only [φ, AddMonoidHom.coe_comp, Function.comp_apply, _root_.GlobalTheory.latticePointHom_apply]
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro P
    obtain ⟨P₁, rfl⟩ := (_root_.GlobalTheory.variableChangePoint_bijective C hC).2 P
    obtain ⟨P₂, rfl⟩ := ringHomPoint_surjective_of_ringEquiv M.ι _ P₁
    obtain ⟨z, rfl⟩ := _root_.GlobalTheory.latticePoint_surjective M.L P₂
    exact ⟨z, hφ z⟩
  · intro z
    rw [hφ, map_eq_zero_iff _ (_root_.GlobalTheory.variableChangePoint_bijective C hC).1,
      ringHomPoint_eq_zero_iff, _root_.GlobalTheory.latticePoint_eq_zero_iff]
  · intro z hz
    have key : ∀ {a b a' b' : ℂ_[q]} (h : M.W.toAffine.Nonsingular a b),
        a = a' → b = b' → ∃ h', (Point.some a b h : M.W.toAffine.Point) =
          Point.some a' b' h' := by
      rintro a b a' b' h rfl rfl
      exact ⟨h, rfl⟩
    have hx : (C.u : ℂ_[q]) ^ 2 * M.ι (M.L.weierstrassP z) + C.r =
        M.ι (M.x z) := by
      show _ = M.ι (M.L.weierstrassP z / M.c ^ 2 -
        M.ι.symm (M.W.b₂ / 12))
      rw [map_sub, map_div₀, map_pow, RingEquiv.apply_symm_apply, hCu, hCr]
      field_simp
      ring
    have hy : (C.u : ℂ_[q]) ^ 3 * M.ι (M.L.derivWeierstrassP z / 2) +
        (C.u : ℂ_[q]) ^ 2 * C.s * M.ι (M.L.weierstrassP z) + C.t =
        M.ι (M.y z) := by
      show _ = M.ι ((M.L.derivWeierstrassP z /
        M.c ^ 3 - M.ι.symm M.W.a₁ *
        M.x z - M.ι.symm M.W.a₃) / 2)
      simp only [map_div₀, map_sub, map_mul, map_pow, RingEquiv.apply_symm_apply, map_ofNat]
      rw [← hx, hCu, hCr, hCs, hCt]
      field_simp
      ring
    rw [hφ, _root_.GlobalTheory.latticePoint_of_notMem M.L hz,
      ringHomPoint_some, _root_.GlobalTheory.variableChangePoint_some]
    exact key _ hx hy

end GlobalTheory.MomOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaVectorsSetupExistsEqSmul
section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators ComplexOrder
open Matrix

namespace GlobalTheory.MomOne.ThetaLine

variable {g : ℕ}

theorem dot_transpose_eq_hf (Hm : Matrix (Fin g) (Fin g) ℂ) (z a : Fin g → ℂ) :
    star a ⬝ᵥ Hmᵀ.mulVec z = hf Hm z a := by
  simp only [dotProduct, mulVec, transpose_apply, hf, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring

theorem im_hf_int {d : ℕ} (hd : 0 < d) (Hm : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ)
    (h : beta d Hm x y ∈ OK d) : ∃ k : ℤ, (hf Hm x y).im = k := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨v, ?_⟩
  have hs : Real.sqrt d / 2 ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    positivity
  have key : (beta d Hm x y).im = Real.sqrt d / 2 * (hf Hm x y).im := by
    rw [beta, Complex.im_ofReal_mul]
  have hv : (beta d Hm x y).im = Real.sqrt d / 2 * v := by
    rw [huv]
    simp [w0, rtd]
    ring
  exact mul_left_cancel₀ hs (key.symm.trans hv)

theorem transl_of_fixed {d : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {x : Fin g → ℂ}
    {G : (Fin g → ℂ) → ℂ} (h : opW d Hm x G = G) (z : Fin g → ℂ) :
    G (z + x) = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ))) *
      Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) * G z := by
  have hz := congrFun h z
  simp only [opW, opU] at hz
  have e1 : Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ))) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ)) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have e2 : Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) *
      Complex.exp (-(Real.pi : ℂ) * hf Hm z x - (Real.pi : ℂ) / 2 * hf Hm x x) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  rw [← hz]
  linear_combination (-(G (z + x) * Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) *
      Complex.exp (-(Real.pi : ℂ) * hf Hm z x - (Real.pi : ℂ) / 2 * hf Hm x x))) * e1 - G (z + x) * e2

theorem exists_eq_smul : ∀ (g : ℕ) (S : Setup g) (e F : (Fin g → ℂ) → ℂ), S.Ok → S.IsTheta e → S.IsTheta F → F ≠ 0 → ∃ c : ℂ, e = c • F := by
  intro g S e F hS he hF hF0
  obtain ⟨hp, -, hH, hdisc, -, -, hβ, hdual⟩ := hS
  have : DiscreteTopology S.La.toAddSubgroup := hdisc
  have hlaw : ∀ G : (Fin g → ℂ) → ℂ, S.IsTheta G → ∀ a ∈ S.La.toAddSubgroup, ∀ z,
      G (z + a) = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta S.d S.Hm a a).re : ℂ))) *
        Complex.exp (Real.pi * (star a ⬝ᵥ S.Hmᵀ.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ S.Hmᵀ.mulVec a)) * G z := by
    intro G hG a ha z
    rw [dot_transpose_eq_hf, dot_transpose_eq_hf]
    exact transl_of_fixed (hG.2 a ha) z
  refine GlobalTheory.ThetaTranslSpan.exists_eq_smul hH.transpose S.La.toAddSubgroup ?_
    (fun a => Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta S.d S.Hm a a).re : ℂ)))) F e ?_
    (hF.1.differentiable (by simp)) hF0 (hlaw F hF) (he.1.differentiable (by simp)) (hlaw e he)
  · intro v
    simp only [dot_transpose_eq_hf]
    exact ⟨hdual v, fun hv a ha => im_hf_int hp.pos S.Hm a v (hβ a ha v hv)⟩
  · intro a _
    simp [Complex.norm_exp]

end GlobalTheory.MomOne.ThetaLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorsionLiftPairingInOrthogonalFrameStatement
section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_lift_pairing_in_orthogonal_frame :
    ∀ (q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (ι : ℂ ≃+* ℂ_[q])
      (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (r : ℕ)
      (b : Fin r → Fin g → ℂ) (n m s s₀ : ℕ) (eps : ℂ) (y : Fin r → Fin (q ^ n)),
      (∀ z : Qbar, ι (z : ℂ) = lam z) → S.Ok → Split S.d q →
      (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) →
      (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → (∀ i, b i ∈ S.La) → IsIdem lam S.d m eps →
      2 * n ≤ m → (s₀ * ∏ i, a i) ∣ s →
      let y' (i : Fin g) : ℂ := beta S.d S.Hm ((s : ℂ) • liftY q n eps b y) (x i) / (a i : ℂ)
      (∀ i, Good ι S.d n s₀ (y' i)) ∧
        ∀ (A : Fin r → ℤ_[q]) (A' : Fin g → ℤ_[q]),
          (∀ i, GlobalTheory.MomOne.zc (A' i) =
            ∑ j, GlobalTheory.MomOne.zc (A j) * ι (beta S.d S.Hm (x i) (b j))) →
          kap S.Hm (vecA n b A) ((s : ℂ) • liftY q n eps b y) ∈ Qbar ∧
            ι (kap S.Hm (vecA n b A) ((s : ℂ) • liftY q n eps b y)) =
              ∏ i, ι (kap1 S.d 1 (y' i)) ^ (PadicInt.toZModPow n (A' i)).val := by
  first | exact @GlobalTheory.MomOne.kapFrame | exact GlobalTheory.MomOne.kapFrame | (intros; apply GlobalTheory.MomOne.kapFrame <;> assumption)
end

