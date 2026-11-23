module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0441
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0941
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2777
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0324

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionKernelEqBaseOnRealUnitaryPoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
namespace GlobalTheory.RealTwistKer

open scoped ComplexConjugate

theorem exists_idele_all {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ)
    {z : D.what₂.Tau → ℂ} (hz : ∀ τ, z τ ≠ 0) :
    ∃ y : (AE D)ˣ, finPart D (y : AE D) = 1 ∧ ∀ τ, θ τ (infPart D (y : AE D)) = z τ := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let a : (D.what₂.Tau → ℂ) → AE D := fun w => 1 + σ (w - 1)
  have a1 : ∀ w, finPart D (a w) = 1 := fun w => by
    simp only [a]
    rw [RingHom.map_add (f := _), hσ.fin, RingHom.map_one, add_zero]
  have a3 : ∀ w τ, θ τ (infPart D (a w)) = w τ := fun w τ => by
    simp only [a]
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp, RingHom.map_one, RingHom.map_one, Pi.sub_apply, Pi.one_apply]
    ring
  have m : a z * a z⁻¹ = 1 := by
    refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
    · rw [RingHom.map_sub, RingHom.map_mul, a1, a1, RingHom.map_one, mul_one, sub_self]
    · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, RingHom.map_one,
        a3, a3, Pi.inv_apply, mul_inv_cancel₀ (hz τ), sub_self]
  exact ⟨⟨a z, a z⁻¹, m, by rw [mul_comm, m]⟩, a1 z, a3 z⟩


set_option maxHeartbeats 800000 in
theorem exists_isDetRoot_pow {D : D7} (V : HSp D) {u : GA D V} (hu : u ∈ GinfC V) (n : ℕ) (hn : 0 < n) :
    ∃ y : (AE D)ˣ, IsDetRoot V u (y ^ n) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨x0, hx0⟩ := (GlobalTheory.Member.isDetRoot_laws D V).1 u
  have hcm := GlobalTheory.Mem.VolExists.isCMExt D.sp.cm
  have einf : ∀ w : AE D, infPart D (sigR (AF D.host.F) D.sp.cm.sig w) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D w) :=
    fun w => GlobalTheory.DetCharArch.map_conj _ _ _
  have efin : ∀ w : AE D, finPart D (sigR (AF D.host.F) D.sp.cm.sig w) = sigR (Af D.host.F) D.sp.cm.sig (finPart D w) :=
    fun w => GlobalTheory.DetCharArch.map_conj _ _ _
  set dt : AE D := (matHom V u).1.det with hdt
  have hfd : finPart D dt = 1 := by
    have h1 : (finHom V u).1.det = finPart D dt := ((finPart D).map_det _).symm
    have h2 : finHom V u = 1 := hu
    rw [← h1, h2]
    simp

  have hd1 : ∀ τ, ‖θ τ (infPart D dt)‖ = 1 := fun τ => by
    have hz : θ τ (infPart D (x0 : AE D)) ≠ 0 := (x0.isUnit.map ((θ τ).comp (infPart D))).ne_zero
    have k : θ τ (infPart D (x0 : AE D)) = θ τ (infPart D (dt * sigR (AF D.host.F) D.sp.cm.sig (x0 : AE D))) :=
      congrArg (fun w => θ τ (infPart D w)) hx0
    rw [RingHom.map_mul, RingHom.map_mul, einf, GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hθ τ)] at k
    have k2 := congrArg norm k
    rw [norm_mul, Complex.norm_conj] at k2
    have hn0 : ‖θ τ (infPart D (x0 : AE D))‖ ≠ 0 := norm_ne_zero_iff.2 hz
    exact (mul_left_eq_self₀.1 k2.symm).resolve_right hn0
  choose s hs using fun τ => IsAlgClosed.exists_pow_nat_eq (θ τ (infPart D dt)) (by omega : 0 < 2 * n)
  have hs1 : ∀ τ, ‖s τ‖ = 1 := fun τ => by
    refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega : 2 * n ≠ 0)).1 ?_
    rw [← norm_pow, hs, hd1]
  have hs0 : ∀ τ, s τ ≠ 0 := fun τ => norm_ne_zero_iff.1 (by rw [hs1]; exact one_ne_zero)
  obtain ⟨y, hy1, hy2⟩ := exists_idele_all hθ hs0
  refine ⟨y, ?_⟩
  show ((y ^ n : (AE D)ˣ) : AE D) = dt * sigR (AF D.host.F) D.sp.cm.sig ((y ^ n : (AE D)ˣ) : AE D)
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, RingHom.map_mul, efin, Units.val_pow_eq_pow_val, RingHom.map_pow, hy1, one_pow, hfd,
      RingHom.map_one, mul_one, sub_self]
  · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_mul, einf,
      GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hθ τ), Units.val_pow_eq_pow_val, RingHom.map_pow, RingHom.map_pow, hy2,
      ← hs τ, map_pow]
    have hc : conj (s τ) * s τ = 1 := by
      rw [mul_comm, Complex.mul_conj', hs1]; simp
    rw [sub_eq_zero, two_mul, pow_add, mul_assoc, ← mul_pow (s τ) (conj (s τ)), mul_comm (s τ) (conj (s τ)), hc, one_pow, mul_one]

end GlobalTheory.RealTwistKer

namespace GlobalTheory.RealTwistKer

theorem weil_kernel_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ u ∈ GinfC (Vc D i), ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ω (u, 1) f = R.ωP i A.μ0 (u, 1) f := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK u hu f hf
  obtain ⟨n, hn, hξn⟩ := hK.fin
  obtain ⟨y, hy⟩ := exists_isDetRoot_pow (Vc D i) hu n hn
  have h := GlobalTheory.TwistFactorProof.weil_ratio (_root_.GlobalTheory.WeilUniq.weilDatum_unique D) (GlobalTheory.WeilChange.exists_weilDatum_twist D)
    (hR.thP.ωP i A.μ0) hK.weil hy (GlobalTheory.TwistFactorProof.isDetRoot_one _) hf
  have hc : ChrEq (χ ^ n) 1 := by
    have := GlobalTheory.ConjTwist.BaseInhab.chrEq_pow hK.chr n hn
    rwa [show ξ ^ n = 1 from hξn] at this
  have e1 : χ (y ^ n) = 1 := by
    rw [map_pow, ← MonoidHom.pow_apply]
    exact GlobalTheory.ChrEqUnique.eq_one_of_chrEq hc y
  have e2 : R.xi A.μ0 (y ^ n) = 1 :=
    GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hR.lev.xi_base ▸ hR.lev.xi A.μ0) _
  have e3 : ∀ j, R.toLevCh.mu A.μ0 j (y ^ n) = R.mu0 j (y ^ n) * R.xi A.μ0 (y ^ n) := fun j => rfl
  rw [h]
  convert one_smul ℂ (R.ωP i A.μ0 (u, 1) f)
  show (((_ * _ : Circle) : ℂ)) = 1
  simp only [Formalism.IndefR.Lift.chrTh, Formalism.IndefR.Lift.tup, MonoidHom.mul_apply, e3, e1, e2, map_one, mul_one, inv_one,
    mul_inv_cancel]
  simp

end GlobalTheory.RealTwistKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTopGridStageExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor NegIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SqTower.TopGridExists


open Matrix in
theorem exists_isONBasis {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {ε : Fin k → Bool}
    (hG : Bᴴ * G * B = Formalism.REAL.Jm ε) (hs : s * B = B * Formalism.REAL.Jm ε) :
    ∃ (B' : Matrix (Fin k) (Fin k) ℂ) (p : ℕ), IsONBasis G s B' p := by
  obtain ⟨π, hπ⟩ := GlobalTheory.FockOrder.exists_sortPerm ε
  generalize (Finset.univ.filter fun a => ε a = true).card = p at hπ
  have hJ : (Matrix.diagonal fun a => (((if ε a then 1 else -1 : ℝ)) : ℂ)) = Formalism.REAL.Jm ε := by
    unfold Formalism.REAL.Jm
    congr 1
    funext a
    cases ε a <;> simp
  refine ⟨B.submatrix id π, p, fun a => if a.val < p then 1 else -1, fun a => ?_, ?_, ?_⟩
  · by_cases ha : a.val < p
    · left; simp [ha]
    · right; simp [ha, not_lt.1 ha]
  · have e : (B.submatrix id π)ᴴ * G * B.submatrix id π = (Bᴴ * G * B).submatrix π π := by
      ext a b; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [e, hG, ← hJ, Matrix.submatrix_diagonal_equiv]
    congr 1; funext a; simp [hπ a]
  · have e : s * B.submatrix id π = (s * B).submatrix id π := by
      ext a b; simp [Matrix.mul_apply]
    rw [e, hs, ← Matrix.submatrix_mul_equiv (e₂ := π), ← hJ, Matrix.submatrix_diagonal_equiv]
    congr 2; funext a; simp [hπ a]


open Matrix GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle in
theorem exists_rig_of_frame {D : D7} {V : HSp D} (A : Fr V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : ∃ r : Rig V, r.Λ = Λ ∧ r.s = A.cart ∧ r.Is := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E V.rank Λ hfull
  have hτ : ∀ τ : D.what₂.Tau, ∃ (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : ℕ),
      IsONBasis (gramAt D V τ) (A.cart τ) B p := fun τ => by
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
    have h1 := Matrix.mul_nonsing_inv _ hu
    refine exists_isONBasis (B := (A.fr τ)⁻¹) (ε := A.ε τ) ?_ ?_
    · rw [← A.fr_gram τ]
      simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.one_mul]
    · simp only [Fr.cart, Matrix.mul_assoc, h1, Matrix.mul_one]
  choose B hB using hτ
  exact ⟨⟨Λ, β, A.cart, B⟩, rfl, rfl, hΛ, hβ, fun τ => ⟨GlobalTheory.CompactFockAction.cart_isCartanInv A τ, hB τ⟩⟩


end GlobalTheory.SqTower.TopGridExists

end
end

