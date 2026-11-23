module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0003
public import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.Bundle0002
public import Formalism.GaussJetBounds.GaussJetProofs.OrbMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.JetTdegEqDegree
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0083
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0094

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeElementComponentMemStandardDoubleCoset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitHecke.HeckeComp

variable {D : D7}

theorem mul_mem_intAE {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem smul_mem_latHat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (L : Set (Fin n → E)) (hL : ∀ u : 𝓞 E, ∀ w ∈ L, (u : E) • w ∈ L) {x : Af F ⊗[F] E} {y : Fin n → Af F ⊗[F] E}
    (hx : x ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)})
    (hy : y ∈ latHat F E L) : x • y ∈ latHat F E L := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, w, hw, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, (u : E) • w, hL u w hw, ?_⟩
      · rw [map_mul]; exact mul_mem (ha v) (hb v)
      · funext i
        rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
    | neg y _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
  | neg y _ h => rw [neg_smul]; exact neg_mem h

theorem smul_mem_LamHat (V : HSp D) {x : Af D.host.F ⊗[D.host.F] D.host.E}
    {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ LamHat V) :
    x • y ∈ LamHat V := by
  refine smul_mem_latHat _ (fun u w hw => ?_) hx hy
  have h1 : ∑ i, ((u : D.host.E) • w) i • V.frame i = (u : D.host.E) • ∑ i, w i • V.frame i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_assoc]
  change ∑ i, ((u : D.host.E) • w) i • V.frame i ∈ V.L0
  rw [h1]
  have h2 := V.L0.smul_mem u hw
  rw [← algebraMap_smul D.host.E u] at h2
  exact h2

theorem det_unit {A O K : Type} [CommRing A] [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) (π : A →+* K) {n : ℕ} (β : GL (Fin n) K)
    (M : Matrix (Fin n) (Fin n) A) {e u u' w : A} (p : O) (k : ℕ) (he1 : π e = 1) (hp : algebraMap O K p = π w)
    (hu : IsInt O (π u)) (hu' : IsInt O (π u')) (huu : e * u * u' = e) (hdet : e * M.det = e * w ^ k * u) :
    ∃ t : Oˣ, ((β⁻¹).1 * M.map π * β.1).det = algebraMap O K (p ^ k * t) := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hu'
  have hab : a * b = 1 := by
    apply hinj
    have h := congrArg π huu
    rw [map_mul, map_mul, he1, one_mul] at h
    rw [map_mul, ha, hb, h, map_one]
  refine ⟨Units.mkOfMulEqOne a b hab, ?_⟩
  have h := congrArg π hdet
  rw [map_mul, map_mul, map_mul, he1, one_mul, one_mul, map_pow, RingHom.map_det] at h
  rw [det_mul, det_mul, mul_right_comm, ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one,
    one_mul, Units.val_mkOfMulEqOne, map_mul, map_pow, hp, ha]
  exact h

theorem fin_mul_mem {e u : AE D} (he : finPart D e ∈ intAE D) (hu : finPart D u ∈ intAE D) :
    finPart D (e * u) ∈ intAE D := by
  have h : finPart D (e * u) = finPart D e * finPart D u := RingHom.map_mul _ e u
  rw [h]
  exact mul_mem_intAE he hu

theorem intM_of_stable {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (hπ : Function.Surjective π) (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)) (hβ : Frame V e π β)
    (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hM : ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ LamHat V →
      (fun i => finPart D (e * (M *ᵥ y) i)) ∈ LamHat V) :
    IntM (Ov D v) ((β⁻¹).1 * M.map π * β.1) := by
  intro i j
  choose y hy using fun k => hπ (β.1 k j)
  have h0 : (fun k => π (y k)) = β.1 *ᵥ Pi.single j 1 := by
    funext k
    rw [hy, mulVec_single_one]
    rfl
  have h1 : (fun i => finPart D (e * y i)) ∈ LamHat V := by
    refine (hβ y).2 fun l => ?_
    rw [h0, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, mulVec_single_one]
    exact intM_one l j
  have h2 := (hβ _).1 (hM y h1) i
  have h3 : (fun k => π ((M *ᵥ y) k)) = M.map π *ᵥ (fun k => π (y k)) := by
    funext k
    exact RingHom.map_mulVec π M y k
  rw [h3, h0, mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at h2
  exact h2

theorem fin_mulVec {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} (e : A)
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) :
    (fun i => φ (e * (M *ᵥ y) i)) = M.map φ *ᵥ (fun i => φ (e * y i)) := by
  funext i
  have h : (fun i => φ (e * y i)) = φ ∘ (e • y) := rfl
  rw [h, ← RingHom.map_mulVec, mulVec_smul]
  rfl

theorem clause_in {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} {e : A} (he : e * e = e)
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) :
    (fun i => φ e * (M.map φ *ᵥ (fun i => φ (e * y i))) i) = fun i => φ (e * (M *ᵥ y) i) := by
  funext i
  rw [← fin_mulVec, ← map_mul, ← mul_assoc, he]

theorem clause_out {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} {e : A} (he : e * e = e) (w : A)
    (M N : Matrix (Fin n) (Fin n) A) (hNM : N * M = 1) (y : Fin n → A) (z : Fin n → B)
    (h : (fun a => φ e * (φ w * φ (e * y a))) = fun a => φ e * (M.map φ *ᵥ z) a) :
    (fun i => φ (e * ((w • N) *ᵥ y) i)) = φ e • z := by
  have h1 : (fun i => φ (e * (w • y) i)) = φ e • (M.map φ *ᵥ z) := by
    funext a
    have h2 : φ e * (φ w * φ (e * y a)) = φ (e * (w • y) a) := by
      rw [← map_mul, ← map_mul, Pi.smul_apply, smul_eq_mul]
      congr 1
      linear_combination (w * y a) * he
    rw [← h2]
    exact congrFun h a
  rw [smul_mulVec, ← mulVec_smul, fin_mulVec, h1, mulVec_smul, mulVec_mulVec, ← Matrix.map_mul, hNM,
    Matrix.map_one _ (map_zero φ) (map_one φ), one_mulVec]


set_option maxHeartbeats 1000000 in
theorem hk_of_isHeckeElt : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ (ϖ : D.host.E) (p : Ov D v) (k : ℕ) (α : GA D V), algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D ϖ) → IsHeckeElt V e ϖ k α → Hk (Ov D v) p k (rho V π β α) := by
  intro D e v π he hc V β hβ ϖ p k α hp hα
  obtain ⟨-, -, hin, hout, u, u', hu, hu', huu, hdet⟩ := hα
  obtain ⟨hs, hker, -, hint⟩ := hc
  have hee : e * e = e := he.1
  have hei : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have he1 : π e = 1 := by
    have h := (hker (1 - e)).2 (by rw [mul_sub, mul_one, hee, sub_self])
    rw [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at h
    exact h.symm
  have hinv : Formalism.L2.Theta.mt V α⁻¹ * Formalism.L2.Theta.mt V α = 1 := by
    change (matHom V α⁻¹).1 * (matHom V α).1 = 1
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [rho_val]
    refine intM_of_stable hs V β hβ _ fun y hy => ?_
    rw [← clause_in (finPart D) hee]
    exact hin _ hy
  · have h1 : algebraMap (Ov D v) (Fv D.host.F v) p • ((rho V π β α)⁻¹).1 =
        (β⁻¹).1 * (incA D ϖ • Formalism.L2.Theta.mt V α⁻¹).map π * β.1 := by
      have h2 : (incA D ϖ • Formalism.L2.Theta.mt V α⁻¹).map π =
          π (incA D ϖ) • (Formalism.L2.Theta.mt V α⁻¹).map π := by
        exact Matrix.ext fun i j => RingHom.map_mul π _ _
      rw [← map_inv, rho_val, h2, hp, Matrix.mul_smul, Matrix.smul_mul]
    rw [h1]
    refine intM_of_stable hs V β hβ _ fun y hy => ?_
    obtain ⟨z, hz, h⟩ := hout _ hy
    rw [clause_out (finPart D) hee (incA D ϖ) _ _ hinv y z h]
    exact smul_mem_LamHat V hei hz
  · rw [rho_val]
    have hinj : Function.Injective (algebraMap (Ov D v) (Fv D.host.F v)) := Subtype.val_injective
    have h1 := (hint u).1 (fin_mul_mem hei hu)
    have h2 := (hint u').1 (fin_mul_mem hei hu')
    exact det_unit hinj π β (Formalism.L2.Theta.mt V α) p k he1 hp h1 h2 huu hdet

end GlobalTheory.SplitHecke.HeckeComp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomeomorphZeroSet
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Topology Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.AffCxPts

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} {k : ℕ}

def coords (φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U)) (y : ↥(CxPts.ptsIn p (RingHom.id ℂ) U)) :
    Fin k → ℂ :=
  fun i => CxPts.ev p (RingHom.id ℂ) U (φ (MvPolynomial.X i)) y.1

theorem evHom_comp (φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U))
    (hC : ∀ a, φ (MvPolynomial.C a) = algX p U a) (y : ↥(CxPts.ptsIn p (RingHom.id ℂ) U)) :
    (CxPts.evHom y.2).comp φ = MvPolynomial.eval (coords φ y) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · rw [RingHom.comp_apply, hC, MvPolynomial.eval_C, ← CxPts.ev_eq y.2, CxPts.ev_algX y.2,
      RingHom.id_apply]
  · rw [RingHom.comp_apply, MvPolynomial.eval_X, coords, CxPts.ev_eq y.2]

def homAt {φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U)} (hφ : Function.Surjective φ) (z : Fin k → ℂ)
    (hz : RingHom.ker φ ≤ RingHom.ker (MvPolynomial.eval z)) : Γ(X, U) →+* ℂ :=
  φ.liftOfSurjective hφ ⟨MvPolynomial.eval z, hz⟩

theorem homAt_comp {φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U)} (hφ : Function.Surjective φ)
    (z : Fin k → ℂ) (hz : RingHom.ker φ ≤ RingHom.ker (MvPolynomial.eval z))
    (P : MvPolynomial (Fin k) ℂ) : homAt hφ z hz (φ P) = MvPolynomial.eval z P :=
  φ.liftOfSurjective_comp_apply hφ ⟨_, hz⟩ P

end GlobalTheory.AffCxPts


open GlobalTheory.AffCxPts GlobalTheory.CxPts GlobalTheory.Points in
theorem GlobalTheory.AffCxPts.homeomorph_zeroSet : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (U : X.Opens),
    IsAffineOpen U → (algX p U).FiniteType → ∃ (k : ℕ) (G : Finset (MvPolynomial (Fin k) ℂ)),
      Nonempty (↥(GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U) ≃ₜ
        ↥{z : Fin k → ℂ | ∀ P ∈ G, MvPolynomial.eval z P = 0}) := by
  intro X p U hU hft
  let := (algX p U).toAlgebra
  obtain ⟨k, φa, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  let φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U) := φa.toRingHom
  have hφ' : Function.Surjective φ := hφ
  have hC : ∀ a, φ (MvPolynomial.C a) = algX p U a := fun a => φa.commutes a
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (RingHom.ker φ) :)
  refine ⟨k, G, ⟨?_⟩⟩
  let Z : Set (Fin k → ℂ) := {z | ∀ P ∈ G, MvPolynomial.eval z P = 0}
  have hker (z : Z) : RingHom.ker φ ≤ RingHom.ker (MvPolynomial.eval (z : Fin k → ℂ)) := by
    rw [← hG]
    exact Ideal.span_le.2 fun P hP => RingHom.mem_ker.2 (z.2 P hP)
  have hψ (z : Z) (a : ℂ) : homAt hφ' z (hker z) (algX p U a) = RingHom.id ℂ a := by
    rw [← hC, homAt_comp, MvPolynomial.eval_C, RingHom.id_apply]
  let s (z : Z) : CxPts p (RingHom.id ℂ) := ofHom hU (homAt hφ' z (hker z)) (hψ z)
  have hs_ev (z : Z) (f : Γ(X, U)) : ev p (RingHom.id ℂ) U f (s z) = homAt hφ' z (hker z) f :=
    ev_ofHom hU _ (hψ z) f
  have hcoords (z : Z) (i : Fin k) :
      ev p (RingHom.id ℂ) U (φ (MvPolynomial.X i)) (s z) = (z : Fin k → ℂ) i := by
    rw [hs_ev, homAt_comp, MvPolynomial.eval_X]
  have htZ (y : ↥(ptsIn p (RingHom.id ℂ) U)) : coords φ y ∈ Z := fun P hP => by
    rw [← evHom_comp φ hC y, RingHom.comp_apply,
      RingHom.mem_ker.1 (hG ▸ Ideal.subset_span hP : P ∈ RingHom.ker φ), map_zero]
  have hgen : Subring.closure (Set.range (ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn p U) ∪
      Set.range fun i : Fin k => φ (MvPolynomial.X i)) = ⊤ := by
    rw [eq_top_iff]
    rintro f -
    obtain ⟨P, rfl⟩ := hφ' f
    induction P using MvPolynomial.induction_on with
    | C a => exact Subring.subset_closure (Or.inl ⟨a, (hC a).symm⟩)
    | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
    | mul_X P i hP =>
      rw [map_mul]; exact mul_mem hP (Subring.subset_closure (Or.inr ⟨i, rfl⟩))
  have hsc : Continuous s := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    refine (PtsOver.tendsto_iff_of_generators hU (ofHom_mem hU _ (hψ z)) hgen).2
      ⟨Eventually.of_forall fun w => ofHom_mem hU _ (hψ w), ?_⟩
    rintro _ ⟨i, rfl⟩
    have e (w : Z) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (s w).1 U (φ (MvPolynomial.X i)) = (w : Fin k → ℂ) i := hcoords w i
    rw [show (fun w : Z => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (s w).1 U (φ (MvPolynomial.X i))) =
        fun w : Z => (w : Fin k → ℂ) i from funext e]
    exact (e z).symm ▸ ((continuous_apply i).comp continuous_subtype_val).tendsto z
  exact
    { toFun := fun y => ⟨coords φ y, htZ y⟩
      invFun := fun z => ⟨s z, ofHom_mem hU _ (hψ z)⟩
      left_inv := fun y => by
        refine Subtype.ext (Subtype.ext (ext_of_valR hU (ofHom_mem hU _ (hψ _)) y.2 fun f => ?_))
        obtain ⟨P, rfl⟩ := hφ' f
        change ev p (RingHom.id ℂ) U (φ P) (s _) = ev p (RingHom.id ℂ) U (φ P) y.1
        rw [hs_ev, homAt_comp, ev_eq y.2, ← RingHom.comp_apply, evHom_comp φ hC y]
      right_inv := fun z => Subtype.ext (funext fun i => hcoords z i)
      continuous_toFun := by
        refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
        exact (continuousOn_iff_continuous_domRestrict.1 (continuousOn_ev (φ (MvPolynomial.X i))))
      continuous_invFun := hsc.subtype_mk _ }
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicPairAdditiveCoordsLinearForms
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)
noncomputable section

namespace GlobalTheory.KerStd.HypOrbit

open Formalism.InvariantFactorPaths.G7 (lgF at1)

theorem lg_flin {p : ℕ} [Fact p.Prime] (hl : 2 ≤ p) {τ m : Type} [Fintype m] (c : m → ℂ_[p]) (v : m → MvPowerSeries τ ℂ_[p])
    (hv : ∀ k, constantCoeff (v k) = 0) :
    PowerSeries.subst (Formalism.L2.Th1.C.flin (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) c v) (lgF ℂ_[p] p) =
      ∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p) := by
  unfold Formalism.L2.Th1.C.flin
  have hA : constantCoeff (∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, constantCoeff_C]
    exact Finset.sum_eq_zero fun k _ => by
      rw [PowerSeries.constantCoeff_subst_eq_zero (hv k) _ (Formalism.L2.Th1.D.Pair.cc_lgF hl), mul_zero]
  rw [← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).1)
    (PowerSeries.HasSubst.of_constantCoeff_zero hA), (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).2.1,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hA)]

theorem cc_flin {p : ℕ} [Fact p.Prime] (hl : 2 ≤ p) {τ m : Type} [Fintype m] (c : m → ℂ_[p]) (v : m → MvPowerSeries τ ℂ_[p])
    (hv : ∀ k, constantCoeff (v k) = 0) :
    constantCoeff (Formalism.L2.Th1.C.flin (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) c v) = 0 := by
  unfold Formalism.L2.Th1.C.flin
  have hA : constantCoeff (∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, constantCoeff_C]
    exact Finset.sum_eq_zero fun k _ => by
      rw [PowerSeries.constantCoeff_subst_eq_zero (hv k) _ (Formalism.L2.Th1.D.Pair.cc_lgF hl), mul_zero]
  exact PowerSeries.constantCoeff_subst_eq_zero hA _ (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).1

theorem hypZ_of_inHyp : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {M N N' r : ℕ} (eA : Fin M ≃ R × Fin N)
    (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p) (Θ : MvPowerSeries (Fin r) ℂ_[p]), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (Formalism.L2.Th1.D.thetaInZ (d := nP D p) p (MaximalUnramifiedExtension p).subtype σ om oms
        (subst (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p]))
          (Formalism.L2.Th1.Top.inHyp p f f'
            (subst (fun i : Fin r => (Formalism.InvariantFactorPaths.G7.at1 i (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) Θ)))) =
      subst (hypZ D p σ om oms R f f') Θ := by
  intro D p _ hp σ om oms R M N N' r eA f f' Θ
  have hl : 2 ≤ p := by omega
  have hcl : PowerSeries.constantCoeff (lgF ℂ_[p] p) = 0 := Formalism.L2.Th1.D.Pair.cc_lgF hl
  have hA0 : HasSubst (fun i : Fin r => (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i hcl
  have hu : ∀ k : ((R × Fin (nP D p / 2)) × Fin N × Fin N') ⊕ ((R × Fin (nP D p / 2)) × Fin N × Fin N'),
      constantCoeff ((Sum.elim (fun e => (X (false, e) : MvPowerSeries (Bool × ((R × Fin (nP D p / 2)) × Fin N × Fin N')) ℂ_[p]))
        (fun e => X (true, e))) k) = 0 := by
    intro k; cases k <;> simp
  have hhc : HasSubst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f') :=
    hasSubst_of_constantCoeff_zero fun i => cc_flin hl _ _ hu

  have hL : ∀ i : Fin r, subst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f')
      (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p]) =
      ∑ e : (R × Fin (nP D p / 2)) × Fin N × Fin N',
        (C ((f e i : MaximalUnramifiedExtension p) : ℂ_[p]) * at1 (false, e) (lgF ℂ_[p] p) +
          C ((f' e i : MaximalUnramifiedExtension p) : ℂ_[p]) * at1 (true, e) (lgF ℂ_[p] p)) := by
    intro i
    rw [Formalism.L2.Th1.D.Pair.subst_single_var hhc]
    unfold Formalism.L2.Th1.E.hypCoord
    rw [lg_flin hl _ _ hu, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    rfl

  set ren1 := (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p])) with hren1
  set Y := (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) with hYdef
  have hR : HasSubst ren1 := hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  have hX : HasSubst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) :=
    hasSubst_of_constantCoeff_zero (CofactorConverse.cc_xOfZ hl _ σ om oms)
  have hY : HasSubst Y := hasSubst_of_constantCoeff_zero fun y => constantCoeff_X _
  have hRX0 : ∀ x, constantCoeff (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x)) = 0 :=
    fun x => constantCoeff_subst_eq_zero hX (CofactorConverse.cc_xOfZ hl _ σ om oms) (constantCoeff_X _)
  have hRX : HasSubst (fun x => subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x)) :=
    hasSubst_of_constantCoeff_zero hRX0
  set W := (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' => subst Y
    (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x))) with hWdef
  have hW : HasSubst W := hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero hY (fun y => constantCoeff_X _) (hRX0 x)
  have hcomp : ∀ g : MvPowerSeries (Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N') ℂ_[p], subst Y (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms)
      (subst ren1 g)) = subst W g := by
    intro g
    rw [subst_comp_subst_apply hR hX, subst_comp_subst_apply hRX hY]
  have hLf : HasSubst (fun i : Fin r => subst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f')
      (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_subst_eq_zero hhc (fun i => cc_flin hl _ _ hu)
      (Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i hcl)

  have hWx : ∀ (c : Bool) (e : (R × Fin (nP D p / 2)) × Fin N × Fin N'), subst W (at1 (c, e) (lgF ℂ_[p] p)) =
      ∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (c, e.1.2) s)) *
        (X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) := by
    intro c e
    rw [Formalism.L2.Th1.D.Pair.subst_single_var hW]
    simp only [hWdef, hren1]
    rw [subst_X hX]
    have ha : PowerSeries.HasSubst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms
        (c, e.1.2, eA.symm (e.1.1, e.2.1), e.2.2)) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (CofactorConverse.cc_xOfZ hl _ σ om oms _)
    rw [← Formalism.L2.Th1.D.Pair.subst_subst1 hY ha]
    have hlog := CofactorConverse.log_xOfZ (d := nP D p) hl (MaximalUnramifiedExtension p).subtype σ om oms (eA.symm (e.1.1, e.2.1)) e.2.2 (c, e.1.2)
    simp only at hlog
    rw [hlog]
    unfold CofactorConverse.linP
    rw [← coe_substAlgHom hY]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul]
    simp only [coe_substAlgHom hY, subst_C]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [subst_X hY]
    simp only [hYdef, Equiv.apply_symm_apply]
  have hEv : ∀ (k : Fin (nP D p / 2)) (q : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N'),
      (∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (false, k) s)) *
        (X (OrbitPlaces.orbMap D p q s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) =
      linEv D p σ (oms k) q a b := by
    intro k q a b
    unfold linEv
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY
    by_cases hs : s.val % 2 = 0 <;> simp [hs]
  have hOd : ∀ (k : Fin (nP D p / 2)) (q : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N'),
      (∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (true, k) s)) *
        (X (OrbitPlaces.orbMap D p q s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) =
      linOd D p σ (om k) q a b := by
    intro k q a b
    unfold linOd
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY
    by_cases hs : s.val % 2 = 0 <;> simp [hs]
  unfold Formalism.L2.Th1.D.thetaInZ Formalism.L2.Th1.Top.inHyp
  rw [hcomp, subst_comp_subst_apply hA0 hhc, subst_comp_subst_apply hLf hW]
  congr 1
  funext i
  rw [hL i]

  rw [← coe_substAlgHom hW]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_add (f := _), map_mul]
  simp only [coe_substAlgHom hW, subst_C, hWx, hEv, hOd]
  rfl

end GlobalTheory.KerStd.HypOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalBasisUnitScalarsExist
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory

theorem locBasisW_clear_den : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ρ : D.host.E →+* ℂ_[p]) (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : Matrix (Fin N) (Fin N) D.host.E) (P' : Matrix (Fin N') (Fin N') D.host.E), L₁.FG → TaylorLogMetric.EqAt D p L L₁ → TaylorLogMetric.EqAt D p L' L₁' → TaylorLogMetric.LocBasisW D ρ L P → TaylorLogMetric.LocBasisW D ρ L' P' → ∃ σ σ' : 𝓞 D.host.E, ‖ρ (σ : D.host.E)‖ = 1 ∧ ‖ρ (σ' : D.host.E)‖ = 1 ∧ (∀ (a : Fin N) (x : Fin N → D.host.E), x ∈ L₁ → ∃ o : 𝓞 D.host.E, (o : D.host.E) = (σ : D.host.E) * ∑ j, P⁻¹ a j * x j) ∧ ∀ b : Fin N', (fun i => (σ' : D.host.E) * P' i b) ∈ L₁' := by
  first
  | exact @_root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers
  | exact _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers
  | (apply _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers ..)

end GlobalTheory
end

