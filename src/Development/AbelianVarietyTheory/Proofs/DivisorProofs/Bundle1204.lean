module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0129
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import ReciprocityTheory.Hypotheses.GalCoh
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardH1EqCardH0MulCardH2

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDiscreteSeriesCharacterEqWeylCharacter
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

noncomputable section

namespace GlobalTheory.WeylPacket

theorem det_rev_pow_eq_vdm {r : ℕ} (a : Fin r → ℂ) :
    (Matrix.of fun i j : Fin r => a i ^ (j.rev : ℕ)).det = Formalism.PacketSums.vdm a := by
  have h2 : (Matrix.of fun i j : Fin r => a i ^ (j.rev : ℕ)) =
      (Matrix.vandermonde (a ∘ Fin.revPerm)).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp [Matrix.vandermonde_apply, Fin.rev_rev]
  have key : ∀ f : Fin r → Fin r → ℂ,
      ∏ i, ∏ j ∈ Finset.Ioi i, f i j = ∏ i, ∏ j, if i < j then f i j else 1 := by
    intro f
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  have key2 : ∀ f : Fin r → Fin r → ℂ,
      ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), f i j = ∏ i, ∏ j, if i < j then f i j else 1 :=
    fun f => Finset.prod_congr rfl fun i _ => Finset.prod_filter _ _
  rw [h2, Matrix.det_submatrix_equiv_self, Matrix.det_vandermonde, Formalism.PacketSums.vdm, key, key2, Finset.prod_comm]
  refine Fintype.prod_equiv Fin.revPerm _ _ fun j => ?_
  refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
  simp [Fin.rev_lt_rev]

theorem det_zpow_eq_sum {r : ℕ} (a : Fin r → ℂ) (m : Fin r → ℤ) :
    (Matrix.of fun i j : Fin r => a i ^ m j).det =
      ∑ w : Equiv.Perm (Fin r), ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, a i ^ m (w⁻¹ i) := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  exact Fintype.prod_equiv w _ _ fun i => by simp

end GlobalTheory.WeylPacket


open GlobalTheory.WeylPacket in
theorem GlobalTheory.dsChar_finsum_eq_glChar : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℤ) (α : Fin n → ℂ) (ι : Type) [Finite ι]
    (y : ι → Equiv.Perm (Fin n)) (θ : ι → Fin n → ℝ), Odd n → Function.Injective α →
    Function.Bijective (fun p : compactWeyl ε × ι => (y p.2)⁻¹ * p.1.1) →
    (∀ q a, Complex.exp (θ q a * Complex.I) = α ((y q)⁻¹ a)) →
    ∑ᶠ q, dsChar ε (fun a => (lam a : ℝ)) (θ q) = glChar (hiWt lam) α := by
  intro n ε lam α ι _ y θ hn hα hb hθ
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨k, hk⟩ := id hn
  set m : Fin n → ℤ := fun a => lam a + (((n - 1) / 2 : ℕ) : ℤ) with hmdef
  have hk2 : (n - 1) / 2 = k := by omega
  have hm : ∀ a, ((fun a => (lam a : ℝ)) a) + ((n : ℝ) - 1) / 2 = (m a : ℝ) := by
    intro a
    have hn' : (n : ℝ) = 2 * k + 1 := by exact_mod_cast hk
    simp only [hmdef, hk2, hn']
    push_cast
    ring
  let WK : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {w | ε ∘ w = ε}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        funext x
        have ha' := congrFun ha (b x)
        have hb' := congrFun hb x
        simp only [Function.comp_apply] at ha' hb' ⊢
        rw [Equiv.Perm.mul_apply, ha', hb']
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        funext x
        have := congrFun ha (a⁻¹ x)
        simp only [Function.comp_apply] at this ⊢
        rw [show a (a⁻¹ x) = x from by simp] at this
        exact this.symm }
  haveI : Fintype WK := Fintype.ofFinite _
  have hmem : ∀ w, w ∈ WK ↔ w ∈ compactWeyl ε := by
    intro w
    show ε ∘ w = ε ↔ _
    simp [compactWeyl]
  have h1 : (1 : Equiv.Perm (Fin n)) ∈ compactWeyl ε := by simp [compactWeyl]
  have hy : Function.Injective y := by
    intro q q' h
    have := hb.1 (a₁ := (⟨1, h1⟩, q)) (a₂ := (⟨1, h1⟩, q')) (by simp [h])
    exact congrArg Prod.snd this
  have hα0 : ∀ i, α i ≠ 0 := by
    intro i
    obtain ⟨⟨w, q⟩, -⟩ := hb.2 1
    have := hθ q (y q i)
    rw [show (y q)⁻¹ (y q i) = i from by simp] at this
    rw [← this]
    exact Complex.exp_ne_zero _
  set T : Finset (Equiv.Perm (Fin n)) := Finset.univ.image y with hT
  let eT : ι ≃ T := Equiv.ofBijective (fun q => ⟨y q, Finset.mem_image_of_mem _ (Finset.mem_univ q)⟩)
    ⟨fun q q' h => hy (congrArg Subtype.val h), fun ⟨g, hg⟩ => by
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hg
      exact ⟨q, rfl⟩⟩
  let e : compactWeyl ε × ι ≃ WK × T :=
    Equiv.prodCongr (Equiv.subtypeEquivRight fun w => (hmem w).symm) eT
  have hbij : Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin n)))⁻¹ * (p.1 : Equiv.Perm (Fin n))) :=
    (Equiv.bijective_comp e _).1 hb
  have hPS := GlobalTheory.packetSum n WK T hbij m α hα0 hα
  have hsign : (-1 : ℂ) ^ halfDim ε = 1 := by
    have hpq := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun a : Fin n => ε a = true)
    simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at hpq
    have := GlobalTheory.signEven _ _ (by rw [hpq]; exact hn)
    rw [halfDim]
    exact_mod_cast this
  have hterm : ∀ q, dsChar ε (fun a => (lam a : ℝ)) (θ q) =
      Formalism.PacketSums.numK WK m (fun i => α ((y q)⁻¹ i)) / Formalism.PacketSums.vdm (fun i => α ((y q)⁻¹ i)) := by
    intro q
    rw [dsChar_eq ε hm (θ q), hsign, one_mul]
    simp only [hθ q]
    congr 1
    · rw [Formalism.PacketSums.numK, Finset.sum_subtype (compactWeyl ε) (fun w => (hmem w).symm)]
      rfl
    · rw [Formalism.PacketSums.vdm]
      exact Finset.prod_congr rfl fun i _ => Finset.prod_congr (by ext j; simp) fun _ _ => rfl
  have hexp : ∀ j : Fin n, hiWt lam j + ((j.rev : ℕ) : ℤ) = m j := by
    intro j
    have := j.isLt
    simp only [hiWt, hmdef, Fin.val_rev]
    omega
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun q _ => hterm q,
    ← Finset.sum_image (f := fun g : Equiv.Perm (Fin n) => Formalism.PacketSums.numK WK m (fun i => α (g⁻¹ i)) /
      Formalism.PacketSums.vdm (fun i => α (g⁻¹ i))) (fun q _ q' _ h => hy h), ← hT, hPS, glChar, det_rev_pow_eq_vdm,
    ← det_zpow_eq_sum]
  congr 2
  ext i j
  simp only [Matrix.of_apply, hexp j]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockPos

theorem differentiable_mul_of_cr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (G E : V → ℂ) (c : V → V → ℂ)
    (hG : Differentiable ℝ G) (hE : Differentiable ℝ E)
    (hGc : ∀ Z Y, fderiv ℝ G Z Y + Complex.I * fderiv ℝ G Z (Complex.I • Y) = -(c Z Y * G Z))
    (hEc : ∀ Z Y, fderiv ℝ E Z Y + Complex.I * fderiv ℝ E Z (Complex.I • Y) = c Z Y * E Z) :
    Differentiable ℂ (fun Z => G Z * E Z) := by
  intro Z
  have hL := (hG Z).hasFDerivAt.mul (hE Z).hasFDerivAt
  set L : V →L[ℝ] ℂ := G Z • fderiv ℝ E Z + E Z • fderiv ℝ G Z with hLdef
  have hI : ∀ Y, L (Complex.I • Y) = Complex.I * L Y := fun Y => by
    have h1 := hGc Z Y
    have h2 := hEc Z Y
    simp only [hLdef, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    linear_combination (-(Complex.I * E Z)) * h1 + (-(Complex.I * G Z)) * h2 +
      (E Z * fderiv ℝ G Z (Complex.I • Y) + G Z * fderiv ℝ E Z (Complex.I • Y)) * Complex.I_sq
  have hsm : ∀ (a : ℂ) (Y : V), L (a • Y) = a * L Y := fun a Y => by
    have e : a • Y = a.re • Y + a.im • (Complex.I • Y) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]
      congr 1
      exact (Complex.re_add_im a).symm
    rw [e, map_add L, L.map_smul, L.map_smul, hI, Complex.real_smul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im a]
    ring
  let g : V →L[ℂ] ℂ :=
    { toFun := fun Y => L Y
      map_add' := fun Y Y' => L.map_add Y Y'
      map_smul' := fun a Y => hsm a Y
      cont := L.continuous }
  exact (differentiableAt_iff_restrictScalars ℝ hL.differentiableAt).2 ⟨g, by rw [hL.fderiv]; ext Y; rfl⟩

theorem gauss_cr {ι : Type} [Fintype ι] {m n : ℕ} (r : ℝ) :
    Differentiable ℝ (fun Z : ι → Fin m → Fin n → ℂ =>
      Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) ∧
    ∀ Z Y : ι → Fin m → Fin n → ℂ,
      fderiv ℝ (fun Z : ι → Fin m → Fin n → ℂ =>
          Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) Z Y +
        Complex.I * fderiv ℝ (fun Z : ι → Fin m → Fin n → ℂ =>
          Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) Z (Complex.I • Y) =
      (2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ) *
        Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) := by
  let P : ι → Fin m → Fin n → ((ι → Fin m → Fin n → ℂ) →L[ℝ] ℂ) := fun τ a b =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) b).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin m → Fin n → ℂ) τ))
  have hP : ∀ τ a b (Z : ι → Fin m → Fin n → ℂ), P τ a b Z = Z τ a b := fun _ _ _ _ => rfl
  have hq : ∀ Z : ι → Fin m → Fin n → ℂ, HasFDerivAt (fun Z : ι → Fin m → Fin n → ℂ => ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2)
      (∑ τ, ∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (Z τ a b)).comp (P τ a b)) Z := fun Z => by
    refine HasFDerivAt.fun_sum fun τ _ => HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ => ?_
    exact (P τ a b).hasFDerivAt.norm_sq
  have hE : ∀ Z : ι → Fin m → Fin n → ℂ, HasFDerivAt (fun Z : ι → Fin m → Fin n → ℂ =>
      Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ))
      (Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) •
        Complex.ofRealCLM.comp ((Real.pi * r) • ∑ τ, ∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (Z τ a b)).comp (P τ a b))) Z :=
    fun Z => (Complex.ofRealCLM.hasFDerivAt.comp Z ((hq Z).const_mul (Real.pi * r))).cexp
  refine ⟨fun Z => (hE Z).differentiableAt, fun Z Y => ?_⟩
  rw [(hE Z).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, smul_eq_mul, Complex.ofRealCLM_apply, innerSL_apply_apply, hP, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, nsmul_eq_mul]
  have key : ∀ z y : ℂ, z * starRingEnd ℂ y =
      ((inner ℝ z y : ℝ) : ℂ) + Complex.I * ((inner ℝ z (Complex.I * y) : ℝ) : ℂ) := by
    intro z y
    rw [Complex.inner, Complex.inner]
    apply Complex.ext <;> simp <;> ring
  simp_rw [key]
  push_cast
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem trace_frames {m n : ℕ} (GS B : Matrix (Fin n) (Fin n) ℂ) (GT B' : Matrix (Fin m) (Fin m) ℂ)
    (hB : Bᴴ * GS * B = 1) (hB' : B'ᴴ * GT * B' = 1) (Z Y : Matrix (Fin m) (Fin n) ℂ) :
    (GS⁻¹ * (B' * Y * B⁻¹)ᴴ * GT * (B' * Z * B⁻¹)).trace = ∑ a, ∑ b, Z a b * starRingEnd ℂ (Y a b) := by
  have e : GS⁻¹ * (B' * Y * B⁻¹)ᴴ * GT * (B' * Z * B⁻¹) = (GS⁻¹ * (B⁻¹)ᴴ) * (Yᴴ * Z) * B⁻¹ := by
    calc _ = GS⁻¹ * (B⁻¹)ᴴ * Yᴴ * (B'ᴴ * GT * B') * Z * B⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hB', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e2 : B⁻¹ * (GS⁻¹ * (B⁻¹)ᴴ) = 1 := by
    rw [Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hB, inv_one]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, e2, Matrix.one_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

end GlobalTheory.FockPos

open GlobalTheory.FockCompare GlobalTheory.VacUnique

noncomputable section

namespace GlobalTheory.FockPos

variable {D : D7}

def frLin {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) :
    Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank →L[ℂ] RW T S :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z τ => (frAt frT τ * Matrix.of (Z τ) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ)
      map_add' := fun Y Z => by
        funext τ
        show (frAt frT τ * (Matrix.of (Y τ) + Matrix.of (Z τ)) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ) = _ + _
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c Z => by
        funext τ
        show (frAt frT τ * (c • Matrix.of (Z τ)) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ) = c • _
        rw [Matrix.mul_smul, Matrix.smul_mul] }

theorem frLin_apply {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank) (τ : D.what₂.Tau) :
    frLin frS frT Z τ = (frAt frT τ * Matrix.of (Z τ) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ) := rfl

theorem norm_embedding_xi0_eq (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = Formalism.L2.Pj.xiR D := by
  have hs : ∀ τ : D.host.E →+* ℂ, ‖τ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    intro τ
    have h0 : (τ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
    rw [← Real.sqrt_sq (norm_nonneg (τ D.host.sqrtMinusD)), ← norm_pow, h0, norm_neg, Complex.norm_natCast]
  unfold Formalism.L2.Pj.xiR Host.xi0
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul,
    Complex.norm_natCast, hs]

theorem xi_zero_eq_host (τ : D.what₂.Tau) : tauE D τ D.host.xi0 = Complex.I * (Formalism.L2.Pj.xiR D : ℂ) := by
  have h1 := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
  have h2 := Formalism.L2.Theta.xi_zero_im_pos D τ
  have h3 : ‖tauE D τ D.host.xi0‖ = Formalism.L2.Pj.xiR D := norm_embedding_xi0_eq D (tauE D τ)
  have h4 : (tauE D τ D.host.xi0).im = Formalism.L2.Pj.xiR D := by
    rw [← h3, Complex.norm_def, Complex.normSq_apply, h1, zero_mul, zero_add, Real.sqrt_mul_self_eq_abs,
      abs_of_pos h2]
  apply Complex.ext <;> simp [h1, h4]

theorem vacuum_real_entire : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS LT f → ∃ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ ∧ ∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w) := by
  intro D ψ θ S T frS frT LS LT hS hT f hf
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hf.2.inf
  obtain ⟨hF, hann⟩ := GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hf.1 S T (fun _ => 1) (fun _ => 1) f
    hf.2.theta hf.2.fock
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hFdef
  set X := frLin frS frT with hX
  set r := Formalism.L2.Pj.xiR D with hr
  set E : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ := fun Z =>
    Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) with hE
  have hU : ∀ {k : ℕ} (fr : GL (Fin k) D.host.E) τ, IsUnit (frAt fr τ).det := fun fr τ =>
    isUnit_iff_ne_zero.2 (frAt_det_ne fr τ)
  have hG : Differentiable ℝ (fun Z => F (X Z)) := hF.comp (X.restrictScalars ℝ).differentiable
  have hdG : ∀ Z Y, fderiv ℝ (fun Z => F (X Z)) Z Y = fderiv ℝ F (X Z) (X Y) := fun Z Y => by
    have h : HasFDerivAt (fun Z => F (X Z)) ((fderiv ℝ F (X Z)).comp (X.restrictScalars ℝ)) Z :=
      (hF (X Z)).hasFDerivAt.comp Z (X.restrictScalars ℝ).hasFDerivAt
    rw [h.fderiv]
    rfl
  refine ⟨fun Z => F (X Z) * E Z,
    differentiable_mul_of_cr (fun Z => F (X Z)) E
      (fun Z Y => (2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ))
      hG (gauss_cr r).1 (fun Z Y => ?_) (gauss_cr r).2, fun w hw => ?_⟩
  · rw [hdG, hdG]
    have hj : jO S T (fun _ => 1) (fun _ => 1) (X Y) = X (Complex.I • Y) := by
      rw [X.map_smul]
      funext τ
      rw [jO_apply]
      change Complex.I • ((1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) * Matrix.of (X Y τ) *
        (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) = _
      rw [Matrix.one_mul, Matrix.mul_one]
      rfl
    have h := hann (X Z) (X Y)
    rw [hj] at h
    have hom : ∀ Y' : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank, omO S T (X Z) (X Y') =
        ∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y' τ a b)).re := by
      intro Y'
      rw [omO_apply]
      refine Finset.sum_congr rfl fun τ _ => ?_
      show 2 * (tauE D τ D.host.xi0 * hAt S T τ (X Z τ) (X Y' τ)).re = _
      unfold hAt
      rw [hX, frLin_apply, frLin_apply, trace_frames _ _ _ _ (frAt_on frS hS τ) (frAt_on frT hT τ), xi_zero_eq_host τ]
      rfl
    rw [hom, hom] at h
    have hs2 : ∀ τ, (∑ a, ∑ b, Z τ a b * starRingEnd ℂ ((Complex.I • Y) τ a b)) =
        -Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) := fun τ => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    simp only [hs2] at h
    have key : ((∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)).re : ℝ) : ℂ) +
        Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * (-Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b))).re : ℝ) : ℂ) =
        2 * Complex.I * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) := by
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      set s := ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)
      apply Complex.ext <;> simp <;> ring
    show _ = -((2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ) * F (X Z))
    have h' : fderiv ℝ F (X Z) (X Y) - Real.pi * Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)).re : ℝ) : ℂ) * F (X Z) +
      Complex.I * (fderiv ℝ F (X Z) (X (Complex.I • Y)) - Real.pi * Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * (-Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b))).re : ℝ) : ℂ) * F (X Z)) = 0 := h
    linear_combination h' + Real.pi * Complex.I * F (X Z) * key +
      2 * Real.pi * r * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)) * F (X Z) * Complex.I_sq
  · have e1 : X (zCo θ frS frT w) = piW θ T S w := by
      funext τ
      rw [hX, frLin_apply]
      change frAt frT τ * ((frAt frT τ)⁻¹ * compAt θ τ w * frAt frS τ) * (frAt frS τ)⁻¹ = _
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    show f w = gaussO θ frS frT w * (f (iotaW σ T S (X (zCo θ frS frT w))) * E (zCo θ frS frT w))
    rw [e1, hσ.iota_pi hw, ← mul_assoc, mul_comm _ (f w), mul_assoc, hE, gaussO, ← Complex.exp_add]
    have e2 : -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ) +
        ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rw [hr]; push_cast; ring
    rw [e2, Complex.exp_zero, mul_one]

end GlobalTheory.FockPos

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLeShiftOfSmallSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.FsTop

variable {X : Scheme.{0}} [IsIntegral X]

theorem regAt_mul' {x : X} {a b : X.functionField} (ha : RegAt x a) (hb : RegAt x b) : RegAt x (a * b) := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  exact ⟨u * v, map_mul _ u v⟩

theorem regAt_inv_of_unitAt {x : X} {a : X.functionField} (ha : UnitAt x a) : RegAt x a⁻¹ := by
  obtain ⟨u, hu, rfl⟩ := ha
  refine ⟨(hu.unit⁻¹ : (X.presheaf.stalk x)ˣ), ?_⟩
  refine (eq_inv_of_mul_eq_one_left ?_)
  rw [← map_mul]
  simp

end GlobalTheory.HSNef.FsTop


open GlobalTheory.HSNef.FsTop in
theorem GlobalTheory.HSNef.le_shift_of_isFS : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M B : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → SmallFam B f w → Le M (B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl) := by
  intro k _ X _ p M B J _ f w hM hB
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hM
  obtain ⟨β, hβ, hbreg, hbnorm⟩ := hB
  have key : ∀ (x : X) (c : B.B.ι) (d : M.B.ι), x ∈ B.B.U c → x ∈ M.B.U d →
      RegAt x ((β c : X.functionField) / (ρ d : X.functionField)) := by
    intro x c d hc hd
    obtain ⟨l, hl⟩ := (hreg x d hd).2
    have hfl : f l ≠ 0 := fun h => hl.ne_zero (by rw [h, zero_mul])
    have e : (β c : X.functionField) / (ρ d) = (f l * β c) * (f l * ρ d)⁻¹ := by
      field_simp
    rw [e]
    exact regAt_mul' (hbreg x c hc l) (regAt_inv_of_unitAt hl)
  refine (_root_.GlobalTheory.HSNef.le_iff_local k X p _ M).2 ⟨β, ρ, hβ, hρ, fun x i j hi hj => key x i j hi hj, ?_⟩
  intro σ y i j hi hj
  have hxi : under y ∈ B.B.U i := mem_ptsIn.1 hi
  have hxj : under y ∈ M.B.U j := mem_ptsIn.1 hj
  have hq := key _ i j hxi hxj
  obtain ⟨l₀, hl₀⟩ := (hreg _ j hxj).2
  set q : X.functionField := (β i : X.functionField) / (ρ j : X.functionField) with hqdef
  have hval : ∀ l, ratVal (f l * (β i : X.functionField)) y = ratVal q y * ratVal (f l * (ρ j : X.functionField)) y := by
    intro l
    have e : f l * (β i : X.functionField) = q * (f l * (ρ j : X.functionField)) := by
      rw [hqdef]; field_simp
    rw [e, ratVal_mul hq ((hreg _ j hxj).1 l)]
  have hφj : (M.φ σ).φ j y = Real.log (∑ l, ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l)) :=
    hφ σ y j hj
  have hφi : ((B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl).φ σ).φ i y =
      (B.φ σ).φ i y + 2 * (Real.log (Fintype.card J) / 2) := rfl
  set S := ∑ l, ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l) with hS
  set φB := (B.φ σ).φ i y
  set Q := ‖ratVal q y‖
  have hn : (1 : ℝ) ≤ Fintype.card J := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨l₀⟩
  have hSpos : 0 < S := by
    have h0 : 0 < ‖ratVal (f l₀ * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l₀) :=
      mul_pos (pow_pos (norm_pos_iff.2 (ratVal_ne_zero hl₀)) 2) (Real.exp_pos _)
    exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun l => ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
      (fun l _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (Finset.mem_univ l₀))

  have hterm : ∀ l, Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l)) ≤ Real.exp φB := by
    intro l
    have h1 := hbnorm σ y i hi l
    rw [hval l, norm_mul] at h1
    have h2 : Q * ‖ratVal (f l * (ρ j : X.functionField)) y‖ ≤ Real.exp (-w l) * Real.exp (φB / 2) := by
      have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (φB / 2)).le
      rwa [mul_assoc, ← Real.exp_add, show -φB / 2 + φB / 2 = 0 by ring, Real.exp_zero, mul_one] at this
    have h3 := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h2 2
    have e1 : (Real.exp (-w l) * Real.exp (φB / 2)) ^ 2 * Real.exp (2 * w l) = Real.exp φB := by
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1; push_cast; ring
    calc Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
        = (Q * ‖ratVal (f l * (ρ j : X.functionField)) y‖) ^ 2 * Real.exp (2 * w l) := by ring
      _ ≤ (Real.exp (-w l) * Real.exp (φB / 2)) ^ 2 * Real.exp (2 * w l) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = Real.exp φB := e1
  have hsum : Q ^ 2 * S ≤ Fintype.card J * Real.exp φB := by
    rw [hS, Finset.mul_sum]
    calc ∑ l, Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
        ≤ ∑ _l : J, Real.exp φB := Finset.sum_le_sum fun l _ => hterm l
      _ = Fintype.card J * Real.exp φB := by simp
  rw [hφi, hφj]
  have hE : Real.exp (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2) ^ 2 =
      S / (Fintype.card J * Real.exp φB) := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2)
        = Real.log S - (Real.log (Fintype.card J) + φB) by push_cast; ring,
      Real.exp_sub, Real.exp_add, Real.exp_log hSpos, Real.exp_log (by linarith)]
  have hpos : 0 ≤ Q * Real.exp (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2) :=
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine (pow_le_one_iff_of_nonneg hpos two_ne_zero).1 ?_
  rw [mul_pow, hE, ← mul_div_assoc, div_le_one (by positivity)]
  exact hsum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoceulerHolds
section
namespace GlobalTheory.Laid

theorem loceuler_holds : ReciprocityTheory.Gal.LocalEulerChar := GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds

end GlobalTheory.Laid
end

