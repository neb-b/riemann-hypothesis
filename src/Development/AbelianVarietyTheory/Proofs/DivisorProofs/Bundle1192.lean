module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistCutInequalitiesStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M M' : LB X) (hB : B.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (s : B.Sec), Mono (cutHom F hB s) → cls M hM = cls M' hM' + cls B hB → (∀ i, hdim k (twist F M) i ≤ hdim k (twist F M') i + hdim k (twist (cut F hB s) M) i) ∧ (∀ i, hdim k (twist F M') (i + 1) ≤ hdim k (twist (cut F hB s) M) i + hdim k (twist F M) (i + 1)) ∧ hdim k (twist F M') 0 ≤ hdim k (twist F M) 0 := by
  first | exact @GlobalTheory.hdim_twist_cut_inequalities | exact GlobalTheory.hdim_twist_cut_inequalities | (intros; apply GlobalTheory.hdim_twist_cut_inequalities <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistPushforwardClosedImmersioStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafCohomologyDim_twist_pushforward_closedImmersion : ∀ (k : Type) [Field k] (X Z : Scheme.{0}) [Algebra k Γ(X, ⊤)] (g : Z ⟶ X) [IsClosedImmersion g] (L : LB X), L.IsLB → ∀ (G : Z.Modules) (m i : ℕ), letI := algebraΓAlong k g; hdim k (twist ((Scheme.Modules.pushforward g).obj G) (lbPow L m)) i = hdim k (twist G (lbPow (L.pull g) m)) i := by
  first | exact @GlobalTheory.hdim_twist_pushforward_lbPow_of_isClosedImmersion | exact GlobalTheory.hdim_twist_pushforward_lbPow_of_isClosedImmersion | (intros; apply GlobalTheory.hdim_twist_pushforward_lbPow_of_isClosedImmersion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.SmallBall

theorem nsq_shift_pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (m : ℕ) (σ : k →+* ℂ) (f : (L.pow m).B.ι → CxPts p σ → ℂ)
    (y : CxPts p σ) :
    (((L.shift t ht).pow m).φ σ).nsq f y = ((L.pow m).φ σ).nsq f y * Real.exp (-(2 * m * t σ)) := by
  simp only [Weight.nsq, HermLB.pow, HermLB.shift, Weight.pow]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  simp only [Weight.addFn]
  congr 2
  push_cast
  ring

theorem mul_exp_le_one_iff (x c d : ℝ) (h : d = 2 * c) : x * Real.exp (-d) ≤ 1 ↔ x ≤ Real.exp c ^ 2 := by
  rw [sq, ← Real.exp_add, ← two_mul, ← h, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos d)]

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f := by
  unfold Pair.nu; positivity

theorem encard_eq_Bl (P : Pair p) {a b : ℤ} {N : HermLB p} (h : P.Rep a b N) (S : Set N.B.Sec) (R : ℝ) (hR : 0 ≤ R)
    (hS : ∀ u, u ∈ S ↔ ∀ σ (y : CxPts p σ), (N.φ σ).nsq (secVal p σ u) y ≤ R ^ 2) :
    S.encard = (P.Bl a b R).encard := by
  obtain ⟨e, he, hr, hn, -⟩ := _root_.GlobalTheory.VolBr.RepDict.rep_dict k X p P a b N h
  have hi : e '' S = P.Bl a b R := by
    ext f
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, fun σ y => ?_⟩
      · have : e u ∈ Set.range e := ⟨u, rfl⟩
        rw [hr] at this
        exact this
      · have h1 := (hS u).1 hu σ y
        rw [← hn] at h1
        exact (pow_le_pow_iff_left₀ (nu_nonneg P a b σ y _) hR two_ne_zero).1 h1
    · rintro ⟨hf, hb⟩
      have : f ∈ Set.range e := by rw [hr]; exact hf
      obtain ⟨u, rfl⟩ := this
      refine ⟨u, (hS u).2 fun σ y => ?_, rfl⟩
      rw [← hn]
      exact pow_le_pow_left₀ (nu_nonneg P a b σ y _) (hb σ y) 2
  rw [← hi, he.encard_image]

theorem main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → ∀ (t : ℝ) (m : ℕ), ((M.shift (fun _ => t) fun _ => rfl).pow m).smallSec.encard = (P.Bl (m * a) (m * b) (Real.exp (t * m))).encard ∧ (M.pow m).smallSec.encard = (P.Bl (m * a) (m * b) 1).encard ∧ (M.shift (fun _ => t) fun _ => rfl).smallSec.encard = (P.Bl a b (Real.exp t)).encard := by
  intro k _ X _ p P a b M hM t m
  have hm := _root_.GlobalTheory.VolBr.Pair.rep_pow k X p P a b M m hM
  refine ⟨?_, ?_, ?_⟩
  · refine encard_eq_Bl P hm _ _ (Real.exp_pos _).le fun u => ?_
    simp only [HermLB.smallSec, Set.mem_setOf_eq]
    refine forall_congr' fun σ => forall_congr' fun y => ?_
    have e := nsq_shift_pow M (fun _ => t) (fun _ => rfl) m σ (secVal p σ u) y
    exact (iff_of_eq (congrArg (· ≤ (1 : ℝ)) e)).trans (mul_exp_le_one_iff _ _ _ (by ring))
  · refine encard_eq_Bl P hm _ _ zero_le_one fun u => ?_
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  · refine encard_eq_Bl P hM _ _ (Real.exp_pos _).le fun u => ?_
    simp only [HermLB.smallSec, Set.mem_setOf_eq]
    refine forall_congr' fun σ => forall_congr' fun y => ?_
    have e := HermLB.nsq_shift M (fun _ => t) (fun _ => rfl) (σ := σ) (secVal p σ u) y
    exact (iff_of_eq (congrArg (· ≤ (1 : ℝ)) e)).trans (mul_exp_le_one_iff _ _ _ (by ring))

end GlobalTheory.VolBr.SmallBall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAdelicGLComplexConjCommutesOperators
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section
namespace GlobalTheory.SmoothConj
open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem chart_conj (φ : GA E a → ℂ) (g : GA E a) :
    chart (fun x => starRingEnd ℂ (φ x)) g = Complex.conjCLE ∘ chart φ g := by
  funext x
  simp only [chart, Function.comp_apply]
  split_ifs <;> simp

theorem conj_mem (φ : Sm E a) : (fun x => starRingEnd ℂ (φ.1 x)) ∈ Sm E a := by
  have hφ : ∀ g, ContDiffOn ℝ (↑(⊤ : ℕ∞)) (chart φ.1 g) (invSet E a) := φ.2
  show ∀ g, ContDiffOn ℝ _ (chart (fun x => starRingEnd ℂ (φ.1 x)) g) (invSet E a)
  intro g
  rw [chart_conj]
  exact Complex.conjCLE.contDiff.comp_contDiffOn (hφ g)

def conjMap (φ : Sm E a) : Sm E a := ⟨fun x => starRingEnd ℂ (φ.1 x), conj_mem φ⟩

def conjEquiv : Sm E a ≃ₗ⋆[ℂ] Sm E a where
  toFun := conjMap
  invFun := conjMap
  map_add' x y := by apply Subtype.ext; funext g; simp [conjMap]
  map_smul' c x := by apply Subtype.ext; funext g; simp [conjMap]
  left_inv x := by apply Subtype.ext; funext g; simp [conjMap]
  right_inv x := by apply Subtype.ext; funext g; simp [conjMap]

theorem conjEquiv_act (o : Op E a) (φ : Sm E a) :
    act o (conjEquiv φ) = conjEquiv (act o φ) := by
  cases o with
  | fin k => rfl
  | cpt k => rfl
  | lie X =>
    apply Subtype.ext; funext g
    show lieD X (fun x => starRingEnd ℂ (φ.1 x)) g = starRingEnd ℂ (lieD X φ.1 g)
    simp only [lieD, chart_conj, ContinuousLinearEquiv.comp_fderiv]
    rfl

end GlobalTheory.SmoothConj

namespace GlobalTheory
open GlobalTheory.CuspRep

theorem smooth_conj_commutes_act : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∃ C : Sm E a ≃ₗ⋆[ℂ] Sm E a, (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) ∧
      ∀ o φ, act o (C φ) = C (act o φ) :=
  fun _ _ _ _ _ => ⟨SmoothConj.conjEquiv, fun _ _ => rfl, SmoothConj.conjEquiv_act⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryFixingPlaneComplementMemClosure
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.PlaneSU

theorem plane_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro F E _ _ _ _ _ σ hCM M J hJ S₁ S₂ ε hε hS e₁ e₂ h12 h11 h22 ⟨t, ht⟩ g hg hfix
  obtain ⟨hσσ, hfixF⟩ := GlobalTheory.CMConjInvol.cm_conj_invol_fixed F E σ hCM
  obtain ⟨hs1, hs2, hBA₀, h1₀, h2₀, hker⟩ := _root_.GlobalTheory.PlaneSU.planeB_facts F E σ hσσ M J hJ e₁ e₂ h12 h11 h22
  obtain ⟨f₁, hf₁⟩ := hfixF _ hs1
  obtain ⟨f₂, hf₂⟩ := hfixF _ hs2
  have hf₁0 : f₁ ≠ 0 := by rintro rfl; exact h11 (by rw [← hf₁, map_zero])
  have hf₂0 : f₂ ≠ 0 := by rintro rfl; exact h22 (by rw [← hf₂, map_zero])
  obtain ⟨δ, bs, hδ, hb0, hb1, hbb⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hCM.2.2.1 hσσ
    (GlobalTheory.HermLineZeros.exists_conj_ne hCM)
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hδ ⟨0, by simp⟩
  have hbq0 : -(f₂ / f₁) ≠ 0 := neg_ne_zero.2 (div_ne_zero hf₂0 hf₁0)

  let ιR : E →+* AF F ⊗[F] E := inclR (F := F) (AF F)
  let ι : AF F →+* AF F ⊗[F] E := algebraMap (AF F) (AF F ⊗[F] E)
  let c : AF F ⊗[F] E →+* AF F ⊗[F] E := sigR (AF F) σ
  let θ : AF F ⊗[F] E := (1 : AF F) ⊗ₜ[F] bs 1
  let A := (planeA e₁ e₂).map ιR
  let B := (planeB σ J e₁ e₂).map ιR
  let H := (planeH σ J e₁ e₂).map ιR
  have hιR : ∀ r : F, ιR (algebraMap F E r) = algebraMap F (AF F ⊗[F] E) r := fun r =>
    (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).commutes r
  have hιF : ∀ r : F, ι (algebraMap F (AF F) r) = algebraMap F (AF F ⊗[F] E) r := fun r =>
    (IsScalarTower.algebraMap_apply F (AF F) (AF F ⊗[F] E) r).symm
  have hcR : ∀ x : E, c (ιR x) = ιR (σ x) := fun x => by simp [c, ιR, sigR, inclR]
  have hcι : ∀ s : AF F, c (ι s) = ι s := StrongApprox.sigR_algebraMap σ
  have hcc : ∀ x, c (c x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [c, sigR, hσσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hcT : ∀ {m p : Type} (P : Matrix m p E), Formalism.UG.cT c (P.map ιR) = (Formalism.UG.cT (σ : E →+* E) P).map ιR := by
    intro m p P; ext i j; simp [Formalism.UG.cT, hcR]
  have hBA : B * A = 1 := by
    simp only [B, A]; rw [← Matrix.map_mul, hBA₀, Matrix.map_one _ (map_zero ιR) (map_one ιR)]
  have h1 : Formalism.UG.cT c A * J.map ιR = H * B := by
    simp only [A, B, H]; rw [hcT, ← Matrix.map_mul, h1₀, Matrix.map_mul]
  have h2 : J.map ιR * A = Formalism.UG.cT c B * H := by
    simp only [A, B, H]; rw [hcT, ← Matrix.map_mul, h2₀, Matrix.map_mul]
  have hH : H = Matrix.diagonal ![algebraMap F (AF F ⊗[F] E) f₁, algebraMap F (AF F ⊗[F] E) f₂] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [H, planeH, ← hf₁, ← hf₂, hιR]
  have hJu : IsUnit (J.map ιR).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hθ : θ * θ = ι (algebraMap F (AF F) δ) := by
    rw [hιF, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hbb]
    exact (hιR δ)
  have hcθ : c θ = -θ := by simp [c, θ, sigR, hb1, TensorProduct.tmul_neg]
  have hbH : ι (algebraMap F (AF F) (-(f₂ / f₁))) * algebraMap F (AF F ⊗[F] E) f₁ =
      -algebraMap F (AF F ⊗[F] E) f₂ := by
    rw [hιF, ← map_mul, ← map_neg]; congr 1; field_simp
  have hιinj : Function.Injective ι :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective

  set G : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
    with hGdef
  have hGu : Formalism.UG.cT c G * J.map ιR * G = J.map ιR := ((show HR (AF F) σ J from g).2)
  have hfixM : G * (1 - A * B) = 1 - A * B :=
    GlobalTheory.T.matrix_fixes_lowRankProjector_of_fixes_rationalKernel F E (AF F) M _ _ hBA₀ G (fun v hv => hfix v ((hker v).1 hv).1 ((hker v).1 hv).2)
  obtain ⟨hGemb, hXu⟩ := GlobalTheory.T.unitary_fixing_kernel_eq_oneAddLowRank_of_unitary _ c hcc M (J.map ιR) hJu A B H hBA h1 h2 G hGu hfixM
  have hdetX : (B * G * A).det = 1 := by
    rw [← det_emb hBA, ← hGemb]; exact StrongApprox.mem_SUAdelic.1 hg
  obtain ⟨x, hxX⟩ := _root_.GlobalTheory.PlaneSU.exists_qm_eq_of_unitary F E σ δ bs hb0 hb1 hbb f₁ f₂ hf₁0 hf₂0 (AF F) (B * G * A) (hH ▸ hXu) hdetX
  have hx1 : nrm x = 1 := by
    apply hιinj
    rw [map_one, ← det_qm ι θ hθ, hxX, hdetX]
  have hpq : ∃ p q : AF F, ε * (algebraMap F (AF F) (-(f₂ / f₁)) - (p ^ 2 - algebraMap F (AF F) δ * q ^ 2)) = 0 := by
    refine _root_.GlobalTheory.PlaneSU.NormSwap.neg_inv_ratio_norm F E σ δ bs hb0 hb1 hbb f₁ f₂ hf₁0 hf₂0 (AF F) ε t ?_
    have e : inclR (F := F) (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂) = algebraMap F (AF F ⊗[F] E) (f₁ / f₂) := by
      rw [← hf₁, ← hf₂, ← map_div₀]; exact hιR _
    rw [← e]; exact ht
  have hxcl : x ∈ closure (H0 (a := δ) (b := -(f₂ / f₁)) ε) :=
    GlobalTheory.T.strongApproximation_quaternion_normOne_split F δ (-(f₂ / f₁)) hδ0 hbq0 S₁ S₂ ε hε hS hpq x hx1

  have hunit : ∀ y : DA F δ (-(f₂ / f₁)), nrm y = 1 →
      Formalism.UG.cT c (emb A B (qm ι θ y)) * J.map ιR * emb A B (qm ι θ y) = J.map ιR := by
    intro y hy
    refine emb_unitary c hBA h1 h2 ?_
    rw [hH]
    exact qm_unitary ι θ c hcι hcθ hθ hbH hy
  have hdet : ∀ y : DA F δ (-(f₂ / f₁)), nrm y = 1 → (emb A B (qm ι θ y)).det = 1 := by
    intro y hy
    rw [det_emb hBA, det_qm ι θ hθ, hy, map_one]
  let Φ : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} → HA (AF F) σ J := fun y =>
    (⟨Matrix.GeneralLinearGroup.mk'' (emb A B (qm ι θ y.1)) (by rw [hdet y.1 y.2]; exact isUnit_one),
      hunit y.1 y.2⟩ : HR (AF F) σ J)
  have hΦmat : ∀ y, ((HA.mat (AF F) σ J (Φ y)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = emb A B (qm ι θ y.1) :=
    fun y => rfl

  have hco : ∀ i, Continuous fun y : DA F δ (-(f₂ / f₁)) => coords y i := fun i =>
    (continuous_apply i).comp continuous_induced_dom
  have hstar : Continuous (star : DA F δ (-(f₂ / f₁)) → DA F δ (-(f₂ / f₁))) := by
    refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
    fin_cases i
    · simpa [coords] using hco 0
    · exact ((hco 1).neg).congr fun y => by simp [coords]
    · exact ((hco 2).neg).congr fun y => by simp [coords]
    · exact ((hco 3).neg).congr fun y => by simp [coords]
  have hE0 := _root_.GlobalTheory.emb_qm_continuous F E δ (-(f₂ / f₁)) M A B θ
  have hnstar : ∀ y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1}, nrm (star y.1) = 1 := fun y => by
    calc nrm (star y.1) = nrm y.1 := by simp [nrm]
      _ = 1 := y.2
  have hinv : ∀ y, ((Φ y)⁻¹ : HA (AF F) σ J) = Φ ⟨star y.1, hnstar y⟩ := by
    intro y
    refine inv_eq_of_mul_eq_one_right ?_
    apply Subtype.ext; apply Units.ext
    change emb A B (qm ι θ y.1) * emb A B (qm ι θ (star y.1)) = 1
    rw [← emb_mul hBA, ← qm_mul ι θ hθ, mul_star_eq, y.2, map_one, qm_one, emb_one]
  have hΦc : Continuous Φ := by
    have hU : Continuous fun y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} => (Φ y : HR (AF F) σ J).1 := by
      refine Units.continuous_iff.2 ⟨hE0.comp continuous_subtype_val, ?_⟩
      have e : (fun y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} =>
          ((((Φ y : HR (AF F) σ J).1)⁻¹ : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) =
          fun y => emb A B (qm ι θ (star y.1)) := by
        funext y
        have := congrArg (fun z : HA (AF F) σ J => (((z : HR (AF F) σ J).1 : GL (Fin M) (AF F ⊗[F] E)) :
          Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) (hinv y)
        exact this
      rw [e]
      exact hE0.comp (hstar.comp continuous_subtype_val)
    exact continuous_induced_rng.2 hU
  have hg_eq : g = Φ ⟨x, hx1⟩ := by
    apply Subtype.ext; apply Units.ext
    change G = emb A B (qm ι θ x)
    rw [hxX]; exact hGemb
  have hH0N : H0 (a := δ) (b := -(f₂ / f₁)) ε ⊆ {y | nrm y = 1} := by
    rintro _ ⟨γ, hγ, h, hh, -, rfl⟩
    simp [nrm_mul, nrm_rat, hγ, hh]
  have hx' : (⟨x, hx1⟩ : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1}) ∈ closure (Subtype.val ⁻¹' H0 ε) := by
    rw [closure_subtype, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype, Set.inter_eq_left.2 hH0N]
    exact hxcl
  have hsub : Φ '' (Subtype.val ⁻¹' H0 ε) ⊆
      {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
    rintro _ ⟨⟨y, hy1⟩, ⟨γ, hγ, h, hh, hεh, hy⟩, rfl⟩
    have hγ1 : nrm (rat γ) = 1 := by rw [nrm_rat, hγ, map_one]
    refine ⟨Φ ⟨rat γ, hγ1⟩, ?_, Φ ⟨h, hh⟩, ?_, ?_⟩
    · refine ⟨StrongApprox.mem_SUAdelic.2 (hdet _ hγ1), ?_⟩
      show HA.mat (AF F) σ J (Φ ⟨rat γ, hγ1⟩) ∈ HFin (AF F) σ J
      have hbE : algebraMap F E (-(f₂ / f₁)) * hE σ J e₁ e₁ = -hE σ J e₂ e₂ := by
        rw [← hf₁, ← hf₂, ← map_mul, ← map_neg]; congr 1; field_simp
      have hdE : IsUnit (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)).det := by
        rw [det_emb hBA₀, det_qm _ _ hbb, hγ, map_one]; exact isUnit_one
      have huE : Formalism.UG.cT (σ : E →+* E) (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)) * J *
          emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ) = J :=
        emb_unitary (σ : E →+* E) hBA₀ h1₀ h2₀
          (qm_unitary (algebraMap F E) (bs 1) (σ : E →+* E) (fun s => σ.commutes s) hb1 hbb hbE hγ)
      refine ⟨Matrix.GeneralLinearGroup.mk'' _ hdE, huE, ?_⟩
      apply Units.ext
      change (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)).map ιR = emb A B (qm ι θ (rat γ))
      rw [emb_map]
      congr 1
      have hcomp : ιR.comp (algebraMap F E) = ι.comp (algebraMap F (AF F)) :=
        RingHom.ext fun r => (hιR r).trans (hιF r).symm
      have e1 : (qm (algebraMap F E) (bs 1) γ).map ιR = qm (ιR.comp (algebraMap F E)) (ιR (bs 1)) γ := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [qm]
      rw [e1, hcomp]
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    · refine ⟨StrongApprox.mem_SUAdelic.2 (hdet _ hh), fun i j => ?_⟩
      have hεε : ε * ε = ε := by
        have h1 : fstA F (ε * ε) = fstA F ε := by
          rw [map_mul]
          funext w
          change fstA F ε w * fstA F ε w = fstA F ε w
          by_cases hw : w ∈ S₁
          · rw [hε.1 w hw, one_mul]
          · rw [hε.2.1 w hw, zero_mul]
        have h2 : sndA F (ε * ε) = sndA F ε := by
          rw [map_mul]
          refine RestrictedProduct.ext _ _ fun v => ?_
          change evalV F v (sndA F ε * sndA F ε) = evalV F v (sndA F ε)
          rw [map_mul]
          by_cases hv : v ∈ S₂
          · rw [hε.2.2.1 v hv, one_mul]
          · rw [hε.2.2.2 v hv, zero_mul]
        exact Prod.ext h1 h2
      have e2 : qm ι θ h - 1 = ι ε • qm ι θ (h - 1) := by rw [← qm_smul, hεh, qm_sub, qm_one]
      have e : emb A B (qm ι θ h) - 1 = ι ε • (A * qm ι θ (h - 1) * B) := by
        unfold emb; rw [add_sub_cancel_left, e2, Matrix.mul_smul, Matrix.smul_mul]
      change ι ε * (emb A B (qm ι θ h) - 1) i j = (emb A B (qm ι θ h) - 1) i j
      rw [e, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, hεε]
    · apply Subtype.ext; apply Units.ext
      change emb A B (qm ι θ y) = emb A B (qm ι θ (rat γ)) * emb A B (qm ι θ h)
      rw [show y = rat γ * h from hy, qm_mul ι θ hθ, emb_mul hBA]
  rw [hg_eq]
  exact closure_mono hsub (image_closure_subset_closure_image hΦc ⟨_, hx', rfl⟩)

end GlobalTheory.PlaneSU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL
open scoped InnerProductSpace

namespace GlobalTheory.SqIntGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem memL2_iff_std {f : GA E a → ℂ} : MemL2Quotient (latticeGL E a) μ f ↔
    LeftInv (latticeGL E a) f ∧ MemLp f 2 (μ.restrict (stdDom (latticeGL E a))) :=
  memL2_iff_fundamental_domain (isFundamentalDomain_stdDom _ μ)

def squareIntegrableSmoothSubmoduleGL : Submodule ℂ (Sm E a) where
  carrier := {ψ | MemL2Quotient (latticeGL E a) μ ψ.1}
  zero_mem' := (memL2_iff_std μ).2 ⟨fun _ _ _ => rfl, MemLp.zero⟩
  add_mem' {x y} hx hy := by
    rw [Set.mem_setOf_eq, memL2_iff_std] at hx hy ⊢
    exact ⟨fun γ hγ g => by simp [hx.1 γ hγ g, hy.1 γ hγ g], hx.2.add hy.2⟩
  smul_mem' c x hx := by
    rw [Set.mem_setOf_eq, memL2_iff_std] at hx ⊢
    exact ⟨fun γ hγ g => by simp [hx.1 γ hγ g], hx.2.const_smul c⟩

theorem mem_l2Sub {ψ : Sm E a} : ψ ∈ squareIntegrableSmoothSubmoduleGL μ ↔ MemL2Quotient (latticeGL E a) μ ψ.1 := Iff.rfl

def l2Map : Sm E a →ₗ[ℂ] L2 (latticeGL E a) μ :=
  toL2ₗ μ (squareIntegrableSmoothSubmoduleGL μ) (fun _ h => (mem_l2Sub μ).1 h) ∘ₗ
    Submodule.linearProjOfIsCompl (squareIntegrableSmoothSubmoduleGL μ) _ (Classical.choose_spec (Submodule.exists_isCompl (squareIntegrableSmoothSubmoduleGL μ)))

theorem l2Map_apply {ψ : Sm E a} (h : ψ ∈ squareIntegrableSmoothSubmoduleGL μ) : l2Map μ ψ = ((mem_l2Sub μ).1 h).toL2 := by
  unfold l2Map
  rw [LinearMap.comp_apply]
  have e := Submodule.linearProjOfIsCompl_apply_left (Classical.choose_spec (Submodule.exists_isCompl (squareIntegrableSmoothSubmoduleGL μ))) ⟨ψ, h⟩
  erw [e]
  rfl

def l2Form : Sm E a →ₗ⋆[ℂ] Sm E a →ₗ[ℂ] ℂ := ((innerₛₗ ℂ).comp (l2Map μ)).compl₂ (l2Map μ)

theorem l2Form_apply {x y : Sm E a} (hx : x ∈ squareIntegrableSmoothSubmoduleGL μ) (hy : y ∈ squareIntegrableSmoothSubmoduleGL μ) :
    l2Form μ x y = ⟪((mem_l2Sub μ).1 hx).toL2, ((mem_l2Sub μ).1 hy).toL2⟫_ℂ := by
  simp only [l2Form, LinearMap.compl₂_apply, LinearMap.comp_apply, l2Map_apply μ hx, l2Map_apply μ hy]
  rfl

theorem re_l2Form_pos {x : Sm E a} (hx : x ∈ squareIntegrableSmoothSubmoduleGL μ) (hc : Continuous x.1) (h0 : x ≠ 0) : 0 < (l2Form μ x x).re := by
  rw [l2Form_apply μ hx hx]
  have : ((mem_l2Sub μ).1 hx).toL2 ≠ 0 := toL2_ne_zero _ hc fun e => h0 (Subtype.ext e)
  first
    | exact (re_inner_self_pos (𝕜 := ℂ)).2 this
    | exact inner_self_pos.2 this
    | exact (RCLike.inner_self_pos).2 this
    | (rw [inner_self_eq_norm_sq_to_K]; norm_cast; simpa using this)

theorem mem_l2Sub_of_isAutForm {ψ : Sm E a} (h : IsAutForm ψ) (h' : IsSqInt ψ.1) : ψ ∈ squareIntegrableSmoothSubmoduleGL μ :=
  memL2_of_isAutForm h h'

end GlobalTheory.SqIntGL

end
end

