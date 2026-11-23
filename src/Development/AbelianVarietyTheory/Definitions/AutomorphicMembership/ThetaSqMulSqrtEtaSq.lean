module

public import Mathlib
public import Formalism.LocalToGlobal.LatticeGeometry.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ChiGen
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRescale
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalForm
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicHolds
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaAndKeyCore

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyPow GlobalTheory.KeyCl

noncomputable section
namespace GlobalTheory.LocM

structure NgC (g : ℕ) : Type where

  τ : Matrix (Fin g) (Fin g) ℂ
  symm : τ.IsSymm
  pos : (τ.map Complex.im).PosDef

  a : Fin g → ℂ

  b : Fin g → ℂ
  half : charHalf g a b

namespace NgC

variable {g : ℕ}

def base (g : ℕ) (a b : Fin g → ℂ) (h : charHalf g a b) : NgC g :=
  ⟨_, (TorusAlg.hypotheses_inhabited.1 g 0 Matrix.isSymm_zero).1,
    (TorusAlg.hypotheses_inhabited.1 g 0 Matrix.isSymm_zero).2, a, b, h⟩

instance (g : ℕ) : Nonempty (NgC g) := ⟨base g 0 0 ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩⟩

def Y (z : NgC g) : Matrix (Fin g) (Fin g) ℝ := z.τ.map Complex.im

def Frame (z : NgC g) (x : KeyIn ℂ) : Prop :=
  ∃ h : x.P.g = g, NormalAt x (z.τ.submatrix (Fin.cast h) (Fin.cast h)) 1
    (fun i => z.a (i.cast h)) (fun i => z.b (i.cast h)) 1

def cubSq (z : NgC g) (w : Fin g → ℂ) : ℝ :=
  ‖thetaChar z.τ z.a z.b w‖ ^ 2 *
    Real.exp (-2 * Real.pi * ((fun i => (w i).im) ⬝ᵥ (z.Y)⁻¹.mulVec fun i => (w i).im))

def thetaSq (z : NgC g) : ℝ :=
  ∫ p in Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1),
    z.cubSq ((fun i => (p (.inl i) : ℂ)) + z.τ.mulVec (fun i => (p (.inr i) : ℂ)))

def lieGram (z : NgC g) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun i j => Real.pi * hermForm ((z.Y)⁻¹.map fun x : ℝ => (x : ℂ))
    (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (Pi.single j (2 * Real.pi * Complex.I)⁻¹)

def etaSq (z : NgC g) : ℝ := (z.lieGram.det.re)⁻¹

theorem lieGram_eq (z : NgC g) :
    z.lieGram = (((4 * Real.pi)⁻¹ • (z.Y)⁻¹ : Matrix (Fin g) (Fin g) ℝ)).map fun x : ℝ => (x : ℂ) := by
  ext i j
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have e : star (Pi.single j (2 * Real.pi * Complex.I : ℂ)⁻¹ : Fin g → ℂ) =
      Pi.single j (-(2 * Real.pi * Complex.I : ℂ)⁻¹) := by
    funext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  simp only [lieGram, Matrix.of_apply, hermForm, e, single_dotProduct, Matrix.mulVec_single, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp
  field_simp
  simp
  ring

theorem etaSq_eq (z : NgC g) : z.etaSq = (4 * Real.pi) ^ g * z.Y.det := by
  have e : z.lieGram.det = ((((4 * Real.pi)⁻¹ • (z.Y)⁻¹ : Matrix (Fin g) (Fin g) ℝ)).det : ℝ) := by
    rw [lieGram_eq]
    exact (RingHom.map_det Complex.ofRealHom _).symm
  rw [etaSq, e, Complex.ofReal_re, Matrix.det_smul, Matrix.det_nonsing_inv, Fintype.card_fin, Ring.inverse_eq_inv',
    mul_inv, inv_inv, inv_pow, inv_inv]

end NgC

structure IsKF (g c : ℕ) (κ : Rule) : Prop where
  homog : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
    (M : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
    (∀ i, IsLieComb (M i) v (v' i)) →
    a ^ (2 * c) * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ c * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩
  funct : Funct κ
  unitSp : UnitSp κ
  off : ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), x.P.g ≠ g → κ K x = 1

namespace IsKF

variable {g c : ℕ} {κ κ' : Rule}

theorem value_normalAt (h : IsKF g c κ) (x : KeyIn ℂ) (hx : x.P.g = g) {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ}
    {a b : Fin x.P.g → ℂ} {c₀ : ℂ} (hc : c₀ ≠ 0) (hM : M.det ≠ 0) (hN : NormalAt x τ M a b c₀) (t : ℂ)
    (ht : ∀ (y : KeyIn ℂ) (e : y.P.g = x.P.g), NormalAt y (τ.submatrix (Fin.cast e) (Fin.cast e)) 1
      (fun i => a (i.cast e)) (fun i => b (i.cast e)) 1 → (κ ℂ y : ℂ) = t) :
    c₀ ^ (2 * c) * (κ ℂ x : ℂ) = M.det ^ c * t := by
  obtain ⟨P, hg, rig, hr, th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, hN₀, e₁, hMv⟩ := KeyConst.exists_rescale P hg rig hr th hth v hv τ M _ _ c₀ hc hM hN
  rw [← ht ⟨P, hg, rig, hr, th₀, hth₀, v₀, hv₀⟩ rfl hN₀]
  exact h.homog ℂ P hg rig hr _ hth₀ v₀ hv₀ th hth v hv c₀ M hx e₁ hMv

theorem ext (h : IsKF g c κ) (h' : IsKF g c κ') (f : NgC g → ℂˣ)
    (hf : ∀ (z : NgC g) x, z.Frame x → κ ℂ x = f z) (hf' : ∀ (z : NgC g) x, z.Frame x → κ' ℂ x = f z) : κ = κ' := by
  funext K _ _ x
  by_cases hx : x.P.g = g
  swap
  · rw [h.off K x hx, h'.off K x hx]
  obtain ⟨K₀, x₀, hK₀, hx₀⟩ := (KeyCountableDescent.keyIn_descends_countable firstFiveLaws.1).2 K x
  obtain ⟨σ⟩ := KeyRuleUnique.nonempty_ringHom_complex K₀
  obtain ⟨y, hy⟩ := exists_keyPB_ring x₀ σ
  have hyg : y.P.g = g := (KeyGalDesc.g_eq hy).trans ((KeyGalDesc.g_eq hx₀).symm.trans hx)
  subst hyg
  obtain ⟨⟨τ, M, a, b, c₀, hab, hc, hM, hN⟩, -⟩ := KeyNormalExists.exists_normalAt thetaUnifAV_all y
  let z : NgC y.P.g := ⟨τ, hN.mem_siegelH.1, hN.mem_siegelH.2, a, b, hab⟩
  have e : (κ ℂ y : ℂ) = κ' ℂ y := by
    refine mul_left_cancel₀ (pow_ne_zero (2 * c) hc) ?_
    rw [h.value_normalAt y rfl hc hM hN (f z) fun w e hw => congrArg Units.val (hf z w ⟨e, hw⟩),
      h'.value_normalAt y rfl hc hM hN (f z) fun w e hw => congrArg Units.val (hf' z w ⟨e, hw⟩)]
  rw [h.funct K₀ ℂ σ x₀ y hy, h'.funct K₀ ℂ σ x₀ y hy] at e
  apply Units.ext
  rw [h.funct K₀ K _ x₀ x hx₀, h'.funct K₀ K _ x₀ x hx₀, σ.injective e]

end IsKF

open Classical in
def cutRule (g : ℕ) (s : ℤˣ) (κ : Rule) : Rule := fun K _ _ x =>
  if x.P.g = g then Units.map (Int.castRingHom K).toMonoidHom s * κ K x else 1

theorem isKF_cutRule {g c : ℕ} (s : ℤˣ) {κ : Rule}
    (hH : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (M : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (M i) v (v' i)) →
      a ^ (2 * c) * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ c * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩)
    (hF : Funct κ) (hU : UnitSp κ) : IsKF g c (cutRule g s κ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M hP h₁ h₂
    simp only [cutRule, ite_eq_left hP, Units.val_mul]
    rw [mul_left_comm, hH K P hg rig hr th hth v hv th' hth' v' hv' a M hP h₁ h₂, mul_left_comm]
  · intro K K' _ _ _ _ f x x' h
    simp only [cutRule, KeyGalDesc.g_eq h]
    split_ifs
    · simp [hF K K' f x x' h]
    · simp
  · intro R K _ _ _ _ _ _ _ x xK h
    by_cases hx : x.P.g = g
    · obtain ⟨u, hu, hk⟩ := hU R K x xK h
      refine ⟨Units.map (Int.castRingHom R).toMonoidHom s * u, ?_, fun k _ _ r xk hr hxk => ?_⟩
      · simp [cutRule, KeyGalDesc.g_eq h, hx, hu]
      · simp [cutRule, KeyGalDesc.g_eq hxk, hx, hk k r xk hr hxk]
    · exact ⟨1, by simp [cutRule, KeyGalDesc.g_eq h, hx],
        fun k _ _ r xk hr hxk => by simp [cutRule, KeyGalDesc.g_eq hxk, hx]⟩
  · intro K _ _ x hx
    exact ite_eq_right hx

structure KF (g c : ℕ) : Type where

  val : NgC g → ℂˣ
  ex : ∃ κ : Rule, IsKF g c κ ∧ ∀ (z : NgC g) (x : KeyIn ℂ), z.Frame x → κ ℂ x = (val z)⁻¹
  zero : g = 0 → ∀ z, val z = 1 ∨ val z = -1

namespace KF

variable {g c : ℕ} (kf : KF g c)

def rule (kf : KF g c) : Rule := kf.ex.choose

def coef (K : Type) [Field K] [CharZero K] (x : KeyIn K) : Kˣ := (kf.rule K x)⁻¹

def norm (z : NgC g) : ℝ := ‖(kf.val z : ℂ)‖ / (z.thetaSq ^ c * Real.sqrt z.etaSq ^ c)

def ofRule (N : ℕ → ℕ) (κ : Rule) (hH : Homog N κ) (hF : Funct κ) (hU : UnitSp κ) (hT : ThetaOne κ) (g : ℕ) :
    KF g (4 * N g) where
  val _ := 1
  ex := ⟨cutRule g 1 κ, isKF_cutRule 1 (fun K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M hP h₁ h₂ => by
      subst hP
      rw [show 2 * (4 * N P.g) = 8 * N P.g by ring]
      exact hH K P hg rig hr th hth v hv th' hth' v' hv' a M h₁ h₂) hF hU, fun z x h => by
    obtain ⟨e, h⟩ := h
    obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := (normalAt_one_iff x _ _ _).1 h
    rw [cutRule, ite_eq_left e, hT x u _ _ _ h₁ h₂ (fun i => z.half.1 _) (fun i => z.half.2 _) h₃ h₄ h₅ h₆]
    simp⟩
  zero _ _ := Or.inl rfl

end KF

def ngTrue : Formalism.L2.Geo.NgPkg where
  NgC := NgC
  NgC_ne _ := inferInstance
  KF := KF
  kfNorm kf z := kf.norm z

theorem exists_kf_four (g : ℕ) : ∃ kf : KF g 4, ∀ z, kf.val z = 1 := by
  obtain ⟨κ, h₁, h₂, h₃, h₄, -⟩ := keyFormula_iff.1 keyFormula_and_keyCore.1
  exact ⟨KF.ofRule (fun _ => 1) κ h₁ h₂ h₃ h₄ g, fun _ => rfl⟩

end GlobalTheory.LocM
end
