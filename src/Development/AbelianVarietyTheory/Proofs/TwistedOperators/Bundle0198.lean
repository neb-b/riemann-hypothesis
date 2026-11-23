module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedLatticeReframeHomMatrixIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.Lat

variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem gram_reS_eq : (reS S b).gram = (frP S b)ᴴ * S.gram * frP S b := by
  refine Matrix.ext fun (i j : Fin S.rank) => ?_
  have hb : ∀ k, b k = ∑ l, frP S b l k • S.frame l := fun k =>
    (Module.Basis.sum_toMatrix_smul_self S.frame b k).symm
  show S.hT (b i) (b j) = ∑ k, (∑ l, star (frP S b l i) * S.gram l k) * frP S b k j
  rw [hb i, hb j]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    HSpace.gram, Finset.sum_mul, Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem sum_frameMatrix_mulVec_smul (s' : Fin S.rank → D.host.E) :
    ∑ k, (frP S b *ᵥ s') k • S.frame k = ∑ a, s' a • b a := by
  have hb : ∀ a, b a = ∑ l, frP S b l a • S.frame l := fun a =>
    (Module.Basis.sum_toMatrix_smul_self S.frame b a).symm
  simp only [hb, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem mem_L0c_iff_mem_intVec_of_span_frame (s' : Fin S.rank → D.host.E) : s' ∈ L0c D (reS S b) ↔ frP S b *ᵥ s' ∈ L0c D S := by
  show ∑ a, s' a • b a ∈ S.L0 ↔ ∑ k, (frP S b *ᵥ s') k • S.frame k ∈ S.L0
  rw [sum_frameMatrix_mulVec_smul]

theorem reW_gen (X : AF D.host.F) (a : D.host.E) (t : Fin T.rank → D.host.E) (s' : Fin S.rank → D.host.E) :
    reW S T b (Matrix.of fun i j => X ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s' k) * (reS S b).gram k j)) =
      Matrix.of fun i j => X ⊗ₜ[D.host.F] (a * t i * ∑ k, star ((frP S b *ᵥ s') k) * S.gram k j) := by
  have h0 : ∀ G' : Matrix (Fin S.rank) (Fin S.rank) D.host.E, G' = (frP S b)ᴴ * S.gram * frP S b →
      (star s' ᵥ* G') ᵥ* frPinv S b = star (frP S b *ᵥ s') ᵥ* S.gram := by
    rintro G' rfl
    rw [Matrix.vecMul_vecMul, Matrix.mul_assoc, frameMatrix_mul_frameMatrixInv, Matrix.mul_one,
      Matrix.star_mulVec, Matrix.vecMul_vecMul]
  have h1 := h0 (reS S b).gram (gram_reS_eq S b)
  have hv : ∀ j, ∑ c, (∑ k, star (s' k) * (reS S b).gram k c) * frPinv S b c j =
      ∑ k, star ((frP S b *ᵥ s') k) * S.gram k j := fun j => congrFun h1 j
  ext i j
  change ∑ c, X ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s' k) * (reS S b).gram k c) * incA D (frPinv S b c j) = _
  rw [Matrix.of_apply, ← hv j, Finset.mul_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  show X ⊗ₜ[D.host.F] _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc]

theorem map_latO (LT : Set (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) :
    (latO (reS S b) T (L0c D (reS S b)) LT P).map (reWHom S T b) = latO S T (L0c D S) LT P := by
  unfold latO
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨w', ⟨α, hα, hP, a, ha, s', hs', t, ht, rfl⟩, rfl⟩
    exact ⟨α, hα, hP, a, ha, _, (mem_L0c_iff_mem_intVec_of_span_frame S b s').1 hs', t, ht, reW_gen S T b _ a t s'⟩
  · rintro ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    have hs' : frP S b *ᵥ (frPinv S b *ᵥ s) = s := by
      rw [Matrix.mulVec_mulVec, frameMatrix_mul_frameMatrixInv, Matrix.one_mulVec]
    refine ⟨_, ⟨α, hα, hP, a, ha, frPinv S b *ᵥ s, (mem_L0c_iff_mem_intVec_of_span_frame S b _).2 (hs'.symm ▸ hs), t, ht, rfl⟩, ?_⟩
    have key : ∀ s' s : Fin S.rank → D.host.E, frP S b *ᵥ s' = s →
        reW S T b (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
          (a * t i * ∑ k, star (s' k) * (reS S b).gram k j)) =
        Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) := by
      rintro s' s rfl
      exact reW_gen S T b _ a t s'
    exact key _ _ hs'

end GlobalTheory.AdSpan.ReVec.Lat


open GlobalTheory.AdSpan.ReVec.Lat in
theorem GlobalTheory.AdSpan.ReVec.latO_reW_iff : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (LT : Set (Fin T.rank → D.host.E)) (u : WO (reS S b) T),
    u ∈ latO (reS S b) T (L0c D (reS S b)) LT (fun _ => True) ↔
      reW S T b u ∈ latO S T (L0c D S) LT (fun _ => True) := by
  intro D S T b LT u
  rw [← map_latO S T b LT]
  exact (AddSubgroup.mem_map_iff_mem (f := reWHom S T b) (reW_bijective S T b).1).symm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecSubMemLatticeCompletionOfLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevExt

variable {D : D7}

theorem intAf_mul {a b : Af D.host.F} (ha : a ∈ intAf D.host.F) (hb : b ∈ intAf D.host.F) :
    a * b ∈ intAf D.host.F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

theorem smul_mem_hatV {k : ℕ} (L : Lt D.host.E k) {a : Af D.host.F} (ha : a ∈ intAf D.host.F) :
    ∀ w ∈ hatV L, a • w ∈ hatV L := by
  intro w hw
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨a * a', intAf_mul ha ha', x, hx, ?_⟩
    funext i
    simp [TensorProduct.smul_tmul', smul_eq_mul]
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem mulVec_sub_mem_hatV : ∀ (D : D7) {k : ℕ} (L L' : Lt D.host.E k) (m : Matrix (Fin k) (Fin k) (AfE D)),
    (∀ x ∈ L, m *ᵥ toAf x - toAf x ∈ hatV L') → ∀ u ∈ hatV L, m *ᵥ u - u ∈ hatV L' := by
  intro D k L L' m h u hu
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    have hy : (fun i => a ⊗ₜ[D.host.F] x i) = a • toAf (D := D) x := by
      funext i
      simp [toAf, TensorProduct.smul_tmul', smul_eq_mul]
    rw [hy, Matrix.mulVec_smul, ← smul_sub]
    exact smul_mem_hatV L' ha _ (h x hx)
  | zero => simp
  | add y z _ _ hy hz =>
    have : m *ᵥ (y + z) - (y + z) = (m *ᵥ y - y) + (m *ᵥ z - z) := by
      rw [Matrix.mulVec_add]; abel
    rw [this]; exact add_mem hy hz
  | neg y _ hy =>
    have : m *ᵥ (-y) - (-y) = -(m *ᵥ y - y) := by
      rw [Matrix.mulVec_neg]; abel
    rw [this]; exact neg_mem hy

end GlobalTheory.LevExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaMapModelsOfNoPairingCovers
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.NoLiftTransfer

theorem jm_mul_jm (p q : ℕ) : Jm p q * Jm p q = 1 := by
  unfold Jm Formalism.UG.Jpq
  simp [Matrix.fromBlocks_multiply]

theorem conj_trace {p q : ℕ} {Z : Mat p q} (hZ : Z ∈ upq p q) : (starRingEnd ℂ) Z.trace = -Z.trace := by
  have h : Zᴴ * Jm p q + Jm p q * Z = 0 := hZ

  have h2 : Jm p q * Zᴴ * Jm p q + Z = 0 := by
    have h' := congrArg (fun X => Jm p q * X) h
    simpa [mul_add, ← mul_assoc, jm_mul_jm] using h'
  have h3 : (Jm p q * Zᴴ * Jm p q).trace + Z.trace = 0 := by rw [← Matrix.trace_add, h2, Matrix.trace_zero]
  rw [Matrix.trace_mul_comm, ← mul_assoc, jm_mul_jm, one_mul, Matrix.trace_conjTranspose] at h3
  rw [starRingEnd_apply]
  exact eq_neg_of_add_eq_zero_left h3

def invConj {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (u : A → B)
    (hb : Function.Bijective u) (hadd : ∀ x y, u (x + y) = u x + u y)
    (hsmul : ∀ (z : ℂ) x, u (z • x) = conj z • u x) : B →ₛₗ[starRingEnd ℂ] A where
  toFun := (Equiv.ofBijective u hb).symm
  map_add' x y := by
    apply hb.1
    rw [hadd]
    simp only [Equiv.ofBijective_apply_symm_apply]
  map_smul' z x := by
    apply hb.1
    rw [hsmul]
    simp only [Equiv.ofBijective_apply_symm_apply, Complex.conj_conj]

theorem invConj_apply {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (u : A → B)
    (hb : Function.Bijective u) (hadd : ∀ x y, u (x + y) = u x + u y)
    (hsmul : ∀ (z : ℂ) x, u (z • x) = conj z • u x) (x : A) : invConj u hb hadd hsmul (u x) = x :=
  hb.1 ((Equiv.ofBijective u hb).apply_symm_apply (u x))

theorem noLift_of_pairNo : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q : ℕ) (T₁ : GrpData p q) (R₁ : DSRep T₁) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (c₁ : ℚ) (b₁ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (u₁ : kfin M τ → R₁.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → PairNo a₁ R₁ → NoLift M τ A pt := by
  intro D V S M τ ι σ Z A pt κ p q T₁ R₁ a₁ l₁ c₁ b₁ e₁ u₁ hK hS hP

  have hsm : ∀ (z : ℂ) x, u₁ (z • x) = conj z • u₁ x := fun z x => by simpa [cjc] using hK.smul z x
  let w := invConj u₁ hK.bij hK.add hsm
  have hw_right : ∀ y, u₁ (w y) = y := fun y => (Equiv.ofBijective u₁ hK.bij).apply_symm_apply y
  have hw_left : ∀ v, w (u₁ v) = v := fun v => invConj_apply u₁ hK.bij hK.add hsm v
  intro U _ _ Q hQ

  let B : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U :=
    { toFun := fun P => (Q (κ.symm P)).comp w
      map_add' := fun P P' => by ext x; simp
      map_smul' := fun z P => by ext x; simp }
  have hB : ∀ P x, B P x = Q (κ.symm P) (w x) := fun _ _ => rfl
  have hinv : PInv a₁ R₁ B := by
    intro Y hY P x
    set t : ℂ := (c₁ : ℂ) * Y.trace with ht_def

    have ht : conj t = -t := by rw [ht_def, map_mul, conj_trace hY, map_ratCast, mul_neg]
    have hX : phiFr (M.fr τ) b₁ e₁ Y ∈ lieAt V τ := by rw [← hK.lie]; exact ⟨Y, hY, rfl⟩
    have hpol : PolDer A pt (phiFr (M.fr τ) b₁ e₁ Y) (κ.symm P) (κ.symm (a₁ Y P + t • P)) :=
      (hS.der Y hY _ _).2 (by simp only [LinearEquiv.apply_symm_apply, ht_def])
    have hvec : VecDer M τ (phiFr (M.fr τ) b₁ e₁ Y) (w x) (w (R₁.HK.act Y x + t • x)) :=
      (hK.der Y hY _ _).2 (by simp only [hw_right, ht_def])
    have h0 := hQ _ hX _ _ _ _ hpol hvec
    have e1 : Q (κ.symm (a₁ Y P + t • P)) (w x) = Q (κ.symm (a₁ Y P)) (w x) + t • Q (κ.symm P) (w x) := by
      rw [map_add (f := _), map_smul, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    have e2 : Q (κ.symm P) (w (R₁.HK.act Y x + t • x)) =
        Q (κ.symm P) (w (R₁.HK.act Y x)) - t • Q (κ.symm P) (w x) := by
      rw [map_add (f := _), map_add (f := _), map_smulₛₗ, ht, map_smul, neg_smul, sub_eq_add_neg]
    rw [e1, e2] at h0
    rw [hB, hB, ← h0]
    abel
  have hB0 : B = 0 := hP U B hinv
  refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
  have h1 := congrArg (fun F : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U => F (κ P) (u₁ v)) hB0
  simpa [hB, hw_left] using h1

end GlobalTheory.ArchRec.NoLiftTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaTensorIntertwinerLowerTowerMembers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.LowerTower

open GlobalTheory.SmallerSource GlobalTheory.FockAlg

theorem lamA_mem (al be ga de : List ℚ) (a : Ix (al.length + be.length) (ga.length + de.length)) :
    lamA al be ga de a ∈ al ++ be ++ ga ++ de := by
  rw [List.append_assoc (al ++ be)]
  cases a with
  | inl i => exact List.mem_append_left _ (GlobalTheory.LowestTypes.getD_mem (List.length_append) i)
  | inr j => exact List.mem_append_right _ (GlobalTheory.LowestTypes.getD_mem (List.length_append) j)

theorem tensNo_first (X : ProvA) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hpq : 1 ≤ p + q) (lam : Ix p q → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair r s) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair r s) (blattner lam) a ≤ 0))
    (hno : ∀ μ', ¬ JointShape p q r s (blattner lam) μ') :
    TensNo (fockAct1 p q r s) (fockAct2 p q r s) (X.ds p q lam) := by
  intro MM f hf
  by_contra hne
  obtain ⟨hadm, hirr⟩ := discrete_series_gk_admissible_irreducible X h5 hpq lam
  obtain ⟨hone, -, hcone⟩ := hD p q lam hlam
  have hex : ∃ v, IsHW (X.ds p q lam).HK.act (blattner lam) v := by
    have hnb : hwSub (X.ds p q lam).HK.act (blattner lam) ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hone
      exact zero_ne_one hone
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnb
    exact ⟨v, hv0, hv⟩
  have hflow := GlobalTheory.T.degW_blattner_le_of_blattnerCone p q (X.ds p q lam).HK lam (cPair r s) θ hcone hsign
  obtain ⟨⟨μ, P, hPJ, hP1, hP2, -⟩, -⟩ :=
    _root_.GlobalTheory.FockAlg.min_first p q r s (X.ds p q lam).HK MM f hirr hadm hf hne (blattner lam) hex hflow
  have hbot := ((GlobalTheory.JointHarm.fock_polynomials X p q r s).2.2.2.2.1 (blattner lam) μ).2 (hno μ)
  have hmem : P ∈ hwSub (X.fock p q r s).act1 (blattner lam) ⊓ hwSub (X.fock p q r s).act2 μ ⊓
      Submodule.span ℂ (X.fock p q r s).J :=
    ⟨⟨hP1.2, hP2.2⟩, Submodule.subset_span hPJ⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hP1.1 hmem

theorem tensNo_second (X : ProvA) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair p q) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair p q) (blattner lam) a ≤ 0))
    (hno : ∀ μ, ¬ JointShape p q r s μ (blattner lam)) :
    TensNo (fockAct2 p q r s) (fockAct1 p q r s) (X.ds r s lam) := by
  intro MM f hf
  set c := TensorProduct.comm ℂ (X.ds r s lam).HK.V MM.V with hc
  have hcm : ∀ (A : Module.End ℂ (X.ds r s lam).HK.V) (B : Module.End ℂ MM.V) x,
      c (TensorProduct.map A B x) = TensorProduct.map B A (c x) := by
    intro A B x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hc]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hg : IsIntw (X.fock p q r s) MM (X.ds r s lam).HK ((c : _ →ₗ[ℂ] _) ∘ₗ f) := by
    refine ⟨fun Z => LinearMap.ext fun P => ?_, fun Z => LinearMap.ext fun P => ?_⟩
    · have := LinearMap.congr_fun (hf.2 Z) P
      simp only [LinearMap.comp_apply] at this
      change c (f (fockAct1 p q r s Z P)) = TensorProduct.map _ _ (c (f P))
      rw [this, hcm]
    · have := LinearMap.congr_fun (hf.1 Z) P
      simp only [LinearMap.comp_apply] at this
      change c (f (fockAct2 p q r s Z P)) = TensorProduct.map _ _ (c (f P))
      rw [this, hcm]
  have h0 := intw_eq_zero X (GlobalTheory.JointHarm.fock_polynomials X) hD h5 hrs lam hlam θ hsign hno MM _ hg
  refine LinearMap.ext fun P => ?_
  have : c (f P) = 0 := LinearMap.congr_fun h0 P
  exact c.map_eq_zero_iff.1 this

theorem no_map_lower : ∀ (X : ProvA), DiscreteSeriesBlattner X → admQ5 X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → ∀ i : ℕ, 1 ≤ i → (i ≤ al.length + de.length + t → i ≤ ga.length + be.length → TensNo (fockAct1 _ _ (al.length + de.length + t - i) (ga.length + be.length - i)) (fockAct2 _ _ _ _) (X.ds _ _ (lamA al be ga de))) ∧ ((∀ x ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |x|) → i ≤ al.length + be.length → i ≤ ga.length + de.length → TensNo (fockAct2 (al.length + be.length - i) (ga.length + de.length - i) _ _) (fockAct1 _ _ _ _) (X.ds _ _ (lamA' t al be ga de))) := by
  intro X hD h5 t al be ga de hA i hi
  have ht : 1 ≤ t := hA.1
  have hn : 1 ≤ al.length + be.length + ga.length + de.length := hA.2.1
  have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
  obtain ⟨-, hpar, hpar', hsign, hsign'⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t al be ga de hA
  obtain ⟨hno, -, hno'⟩ := _root_.GlobalTheory.LowestTypeDrop.lowestType_not_jointShape t al be ga de hA i hi
  refine ⟨fun hr hs => ?_, fun hbig hp hq => ?_⟩
  · refine tensNo_first X hD h5 (by omega) _ hpar 0 ?_ (hno hr hs)
    rw [cPair_sub hr hs]
    refine fun a => ⟨(hsign a).1, fun h => (hsign a).2 (lt_of_le_of_ne h fun h0 => ?_)⟩
    have := hA.2.2.2.2.2.2.2.2.2.2 _ (lamA_mem al be ga de a)
    rw [h0, abs_zero] at this
    linarith
  · refine tensNo_second X hD h5 (by omega) _ hpar' ((t : ℚ) / 2) ?_ (hno' (.inl ?_) hp hq).1
    · rw [cPair_sub hp hq]
      exact hsign'
    · rintro ⟨a, ha⟩
      have := hbig _ (lamA_mem al be ga de a)
      rw [ha, abs_of_nonneg (by positivity)] at this
      linarith

end GlobalTheory.LowerTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

variable {D : D7}

def liftI (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) : Ideal (𝓞 D.host.E) :=
  ∏ PP ∈ Pg ∪ Q, conjI PP.asIdeal

theorem frMapAdj_zero (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    frMapAdj S T βS βT 0 = 0 := by
  unfold frMapAdj
  simp

theorem isIntM_zero {b a : ℕ} : IsIntM (0 : Matrix (Fin b) (Fin a) (EAf D)) := fun _ _ => zero_mem _

theorem redM_frMapAdj_zero (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (PP : Formalism.L2.DIV.Pl D.host.E) : redM PP (frMapAdj S T βS βT 0) = 0 := by
  have h0 : IsIntM (frMapAdj S T βS βT 0) := by rw [frMapAdj_zero]; exact isIntM_zero
  have h := (GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT 0 0 h0 h0).2 PP
  rw [add_zero] at h
  exact (left_eq_add.mp h)

def liftL (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) : AddSubgroup (WO S T) where
  carrier := {x | IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧
    ∀ PP ∈ Pg ∪ Q, redM PP (frMapAdj S T βS βT x) = 0}
  zero_mem' := by
    refine ⟨fun i j => by simp, ?_, fun PP _ => ?_⟩
    · rw [frMapAdj_zero]; exact isIntM_zero
    · exact redM_frMapAdj_zero S T βS βT PP
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT x y hx2 hy2
    refine ⟨fun i j => ?_, h1, fun PP hPP => ?_⟩
    · simp only [Matrix.add_apply, mul_add, hx1 i j, hy1 i j]
    · rw [h2, hx3 PP hPP, hy3 PP hPP, add_zero]
  neg_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    have hneg : frMapAdj S T βS βT (-x) = -frMapAdj S T βS βT x := by
      unfold frMapAdj
      simp [Matrix.map_neg, Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]
    have hI : IsIntM (frMapAdj S T βS βT (-x)) := fun i j => by
      rw [hneg, Matrix.neg_apply]; exact neg_mem (hx2 i j)
    obtain ⟨-, h2⟩ := GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT x (-x) hx2 hI
    refine ⟨fun i j => ?_, hI, fun PP hPP => ?_⟩
    · simp only [Matrix.neg_apply, mul_neg, hx1 i j]
    · have := h2 PP
      rw [add_neg_cancel, redM_frMapAdj_zero, hx3 PP hPP, zero_add] at this
      exact this.symm

def adjA (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (a : AE D) (x : WO S T) :
    Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  toEAf D a • HMul.hMul βS.val (frMapAdj S T βS βT x)

def IsMover (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e a : AE D)
    (k₀ : GA D S) : Prop :=
  k₀ ∈ GfC S ∧ (∀ x : WO S T, IsHalf (1 - e - cA D e) x → actO S T k₀ 1 x = x) ∧
    ∀ x : WO S T, IsHalf (cA D e) x →
      frMapAdj S T βS βT (actO S T k₀ 1 x) = adjA S T βS βT a x

def IsGen {S T : HSp D} (C : Ctx S T) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e a : AE D) : Prop :=
  ∀ x : WO S T, IsHalf (cA D e) x →
    (IsIntM (adjA S T βS βT a x) ↔
      x ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ)) ∧
    ((IsIntM (adjA S T βS βT a x) ∧
      ∀ PP ∈ Pg ∪ Q, redM PP (adjA S T βS βT a x) = 0) ↔
      x ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)))

end GlobalTheory.LiftLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalZetaKernelGLRightInvariantIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalZetaKernelGL_right_invariant_integral : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r N : ℕ) (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), KerGL w N z φ → ∀ g k : GL (Fin r) (w.adicCompletion E), k ∈ KGL w (n := r) → φ (g * k) = φ g := by
  first | exact @GlobalTheory.ZetaGL.kerGL_mul_right_KGL | exact GlobalTheory.ZetaGL.kerGL_mul_right_KGL | (intros; apply GlobalTheory.ZetaGL.kerGL_mul_right_KGL <;> assumption)
end

