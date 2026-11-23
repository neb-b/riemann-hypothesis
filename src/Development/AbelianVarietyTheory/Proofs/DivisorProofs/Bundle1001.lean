module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerThetaFunctionsReadingTestFunctionFrames
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.Overlap

section Kernel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)

theorem kZero_zero (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (x₁ x₂ : Frame X.Ψ r) :
    kZero X idx x₁ x₂ (0 : Fin n → Fin g → ℂ) 0 =
      ∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹ := by
  unfold kZero
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h : ∀ k, dblz X idx x₁ x₂ (0 : Fin n → Fin g → ℂ) 0 τ k = 0 := fun k => by
    have e : (fun a : Fin r => if (a : ℕ) < X.p0 then (0 : Fin n → Fin g → ℂ) k (idx.symm (τ, a))
        else (0 : Fin n → Fin g → ℂ) k (idx.symm (τ, a))) = 0 := by
      funext a
      simp
    funext c
    simp only [dblz, Matrix.of_apply, e, mulVec_zero, smul_zero]
  simp only [h, mulVec_zero, dotProduct_zero, Finset.sum_const_zero, mul_zero, Complex.exp_zero, mul_one]

theorem aLin_move {x₁ x₂ y₁ y₂ : Frame X.Ψ r} (τ : X.Ψ) {u : Matrix (Fin r) (Fin r) ℂ} (hu : IsUnit u.det)
    (hh : ∀ v w, hermC τ.1 X.Gm (u *ᵥ v) (u *ᵥ w) = hermC τ.1 X.Gm v w)
    (h₁ : mat y₁ τ = u * mat x₁ τ) (h₂ : mat y₂ τ = u * mat x₂ τ) :
    aLin X y₁ y₂ τ * u = aLin X x₁ x₂ τ := by
  refine Matrix.ext_of_mulVec_single fun c => ?_
  generalize (Pi.single c 1 : Fin r → ℂ) = w
  funext a
  rw [← mulVec_mulVec]
  by_cases ha : (a : ℕ) < X.p0
  · rw [DblPoint.aLin_mulVec_of_lt X _ _ _ _ ha, DblPoint.aLin_mulVec_of_lt X _ _ _ _ ha, h₂, ← hh w]
    rfl
  · rw [DblPoint.aLin_mulVec_of_not_lt X _ _ _ _ ha, DblPoint.aLin_mulVec_of_not_lt X _ _ _ _ ha, h₁,
      Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem det_move {x₁ x₂ y₁ y₂ : Frame X.Ψ r} (τ : X.Ψ) {u : Matrix (Fin r) (Fin r) ℂ}
    (hu : u.det * conj u.det = 1)
    (hh : ∀ v w, hermC τ.1 X.Gm (u *ᵥ v) (u *ᵥ w) = hermC τ.1 X.Gm v w)
    (h₁ : mat y₁ τ = u * mat x₁ τ) (h₂ : mat y₂ τ = u * mat x₂ τ) :
    (aLin X y₁ y₂ τ).det * (aAnti X y₁ y₂ τ).det = (aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det := by
  have hu' : IsUnit u.det := IsUnit.of_mul_eq_one _ hu
  have e : ∀ z₁ z₂ : Frame X.Ψ r, (aAnti X z₁ z₂ τ).det = conj (aLin X z₂ z₁ τ).det := fun z₁ z₂ => by
    rw [DblPoint.aLin_swap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.conj_conj]
  rw [e, e, ← aLin_move X τ hu' hh h₁ h₂, ← aLin_move X τ hu' hh h₂ h₁, det_mul, det_mul, map_mul]
  linear_combination (-((aLin X y₁ y₂ τ).det * conj (aLin X y₂ y₁ τ).det)) * hu

end Kernel

variable {D : D7} {S T : HSp D} (C : GlobalTheory.Ker.Ctx S T)

theorem kZero_mvB {B B' : C.Bas} (hB : C.IsB B) (u : GA D T) :
    kZero C.X C.idx (C.xB (C.mvB u B)) (C.xB (C.mvB u B')) (0 : Fin S.rank → Fin C.g → ℂ) 0 =
      kZero C.X C.idx (C.xB B) (C.xB B') (0 : Fin S.rank → Fin C.g → ℂ) 0 := by
  rw [kZero_zero, kZero_zero]
  refine Finset.prod_congr rfl fun σ _ => ?_
  obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
  have hU := GlobalTheory.Ker.ONBasis.compAt_unitary C τ u
  have hm : ∀ A : C.Bas, mat (C.xB (C.mvB u A)) (C.m.e τ) =
      (compAt C.θ τ (Formalism.L2.Theta.mt T u)).map conj * mat (C.xB A) (C.m.e τ) := fun A => by
    rw [GlobalTheory.Ker.ONBasis.mat_xB, GlobalTheory.Ker.ONBasis.mat_xB, ← Matrix.map_mul]
    rfl
  generalize compAt C.θ τ (Formalism.L2.Theta.mt T u) = U at hU hm
  have hG : (gramAt D T τ).det ≠ 0 := by
    intro h0
    have h1 := congrArg det (hB τ)
    have h2 := congrArg det (GlobalTheory.Ker.ONBasis.sgnM_sq C.X)
    rw [det_mul, det_mul, h0, mul_zero, zero_mul] at h1
    rw [det_mul, ← h1, zero_mul, det_one] at h2
    exact zero_ne_one h2
  rw [det_move C.X (C.m.e τ) (u := U.map conj) ?_ ?_ (hm B) (hm B')]
  · have h1 := congrArg det hU
    rw [det_mul, det_mul, det_conjTranspose] at h1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.conj_conj]
    apply mul_right_cancel₀ hG
    rw [one_mul]
    refine Eq.trans ?_ h1
    rw [Complex.star_def]
    ring
  · intro v w
    have e : ∀ v : Fin T.rank → ℂ, U.map conj *ᵥ v = fun a => conj ((U *ᵥ star v) a) := fun v => by
      funext a
      simp [mulVec, dotProduct]
    have e' : ∀ v : Fin T.rank → ℂ, v = fun a => conj (star v a) := fun v => by
      funext a
      simp
    rw [e, e, GlobalTheory.Ker.ONBasis.hermC_conj]
    conv_rhs => rw [e' v, e' w, GlobalTheory.Ker.ONBasis.hermC_conj, ← hU]
    rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star (star v)) Uᴴ]

theorem ipO_Th {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {x₁ x₂ : Frame C.X.Ψ T.rank} (h₁ : x₁ ∈ C.X.dom) (h₂ : x₂ ∈ C.X.dom) {φ₁ φ₂ : TF S.rank C.g}
    (s₁ : GlobalTheory.SW.IsSB φ₁) (s₂ : GlobalTheory.SW.IsSB φ₂) :
    GlobalTheory.Ker.ipO μ 𝓕 (C.Th x₁ φ₁) (C.Th x₂ φ₂) =
      dbl C.X C.bas C.idx φ₁ φ₂ 0 * kZero C.X C.idx x₁ x₂ (0 : Fin S.rank → Fin C.g → ℂ) 0 := by
  have h0 : GlobalTheory.Ker.IsRealPt (0 : WO S T) := Matrix.map_zero _ (map_zero _)
  have h := GlobalTheory.Ker.GaussKer.ipO_rho_Th D S T C μ 𝓕 hμ x₁ h₁ x₂ h₂ φ₁ φ₂ s₁ s₂ 0 0 h0 h0
  have hr : ∀ f, C.rho 0 f = f := fun f => by
    funext w
    simp [GlobalTheory.Ker.Ctx.rho, heisO, symplOH, symplO, hO]
  have hz : ∀ x, C.zOf x (0 : WO S T) = 0 := fun x => by
    funext k i
    simp [GlobalTheory.Ker.Ctx.zOf, GlobalTheory.Ker.zR, GlobalTheory.Ker.Ctx.realPt, compAt, hermC, mulVec, dotProduct]
  have hg : ∀ x, GlobalTheory.Ker.gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := fun x => by
    simp [GlobalTheory.Ker.gaussR, hx]
  rw [hr, hr, hz, hz, hg, hg] at h
  have e : (fun (k : Fin S.rank) (i : Fin C.g) => conj ((0 : Fin S.rank → Fin C.g → ℂ) k i)) = 0 := by
    funext k i
    simp
  rw [h, e, map_one, one_mul, one_mul]

theorem isBasOf_unique {W : HSp D} {X : Data D.host.E W.rank} (hm : IsMod W rfl X) {q0 : ℕ}
    (hq : X.p0 + q0 = W.rank) {x : Frame X.Ψ W.rank} {B B' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (h : IsBasOf W rfl X hq x B) (h' : IsBasOf W rfl X hq x B') : B = B' := by
  funext ρ
  ext a i
  have hτ : tauE D ρ ∈ X.Ψ := (hm.psi _).2 ⟨ρ, rfl⟩
  by_cases hi : (i : ℕ) < q0
  · rw [h ρ ⟨_, hτ⟩ rfl (Sum.inl ⟨i, hi⟩) i a rfl, h' ρ ⟨_, hτ⟩ rfl (Sum.inl ⟨i, hi⟩) i a rfl]
  · have h1 : (i : ℕ) - q0 < X.p0 := by have := i.2; omega
    have h2 : (i : ℕ) = q0 + ((i : ℕ) - q0) := by omega
    rw [h ρ ⟨_, hτ⟩ rfl (Sum.inr ⟨_, h1⟩) i a h2, h' ρ ⟨_, hτ⟩ rfl (Sum.inr ⟨_, h1⟩) i a h2]

end GlobalTheory.AdTh.Overlap


open GlobalTheory.AdTh.Overlap in
theorem GlobalTheory.AdTh.inner_of_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∃ G : Frame X.Ψ r → Frame X.Ψ r → ℂ, ∀ x x' : Frame X.Ψ r, IsONFr X x → IsONFr X x' → G x x' ≠ 0 ∧ (∀ u : GA D W, G (frMove θ W hr X u x) (frMove θ W hr X u x') = G x x') ∧ ∀ v : TF V.rank g, GlobalTheory.SW.IsSB v → v ≠ 0 → ∃ c : ℂ, c ≠ 0 ∧ ∀ y y' : Frame X.Ψ r, IsONFr X y → IsONFr X y' → ∀ (f f' : WO V W → ℂ) (κ κ' : ℂ), IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → Reads θ V W hr X bas idx f (κ • v) y → Reads θ V W hr X bas idx f' (κ' • v) y' → ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∫ w in 𝓕, f w * conj (f' w) ∂μ = κ * conj κ' * (c * G y y') := by
  intro D ψ θ V W r g hr X bas idx hstd hinf hV he hm hs
  subst hr
  obtain ⟨X', m, hq', hq, bas', idx', hs', -, -, -, -, -, -, H⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hstd hinf he hV hm hs
  let C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hinf, X', m, g, X.p0, hq', bas', idx', hs', he⟩
  let Bx : Frame X.Ψ W.rank → C.Bas := fun x => Classical.epsilon fun B => IsBasOf W rfl X hq x B
  have hBx : ∀ x, IsONFr X x → IsBasOf W rfl X hq x (Bx x) := fun x hx => Classical.epsilon_spec (H x hx).1
  have hB : ∀ x, IsONFr X x → C.IsB (Bx x) := fun x hx => ((H x hx).2 _ (hBx x hx)).1
  have hd : ∀ x, IsONFr X x → C.xB (Bx x) ∈ C.X.dom := fun x hx =>
    GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C (hB x hx))
  have hmv : ∀ x, IsONFr X x → ∀ u, Bx (frMove θ W rfl X u x) = C.mvB u (Bx x) := fun x hx u => by
    obtain ⟨h1, h2⟩ := ((H x hx).2 _ (hBx x hx)).2.2.2.2.2.2.2.1 u
    exact isBasOf_unique hm hq (hBx _ h1) h2
  have hT : ∀ x, IsONFr X x → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), GlobalTheory.SW.IsSB φ →
      ((IsThetaFunO ψ V W f ∧ Reads θ V W rfl X bas idx f φ x) ↔ f = C.Th (C.xB (Bx x)) φ) := fun x hx =>
    ((H x hx).2 _ (hBx x hx)).2.2.2.2.2.2.2.2
  have hne : ∀ x x', IsONFr X x → IsONFr X x' →
      kZero C.X C.idx (C.xB (Bx x)) (C.xB (Bx x')) (0 : Fin V.rank → Fin g → ℂ) 0 ≠ 0 := fun x x' hx hx' => by
    rw [kZero_zero]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero (pow_ne_zero _ (mul_ne_zero
      (DblPoint.det_aLin_ne_zero (hd x hx) (hd x' hx') τ) (DblPoint.det_aAnti_ne_zero (hd x hx) (hd x' hx') τ)))
  refine ⟨fun x x' => kZero C.X C.idx (C.xB (Bx x)) (C.xB (Bx x')) (0 : Fin V.rank → Fin g → ℂ) 0,
    fun x x' hx hx' => ⟨hne x x' hx hx', fun u => ?_, fun v hv hv0 => ⟨dbl C.X C.bas C.idx v v 0, fun hc => ?_, ?_⟩⟩⟩
  · beta_reduce
    rw [hmv x hx, hmv x' hx']
    exact kZero_mvB C (hB x hx) u
  · obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.Ker.ScalarProduct.ip_basic D V W C
    have h1 := ipO_Th C hμ (hd x hx) (hd x hx) hv hv
    rw [hc, zero_mul] at h1
    have h2 := (hip μ 𝓕 hμ _ ((hT x hx _ v hv).2 rfl).1).2.1 h1
    obtain ⟨l1, l2, -⟩ := GlobalTheory.Ker.Ctx.th_laws D V W C _ (hd x hx) v hv
    have h3 : GlobalTheory.SW.IsSB ((0 : ℂ) • v) := by
      obtain ⟨R, hR, -, -⟩ := hv
      exact ⟨R, hR, fun x hx => absurd (by simp) hx, fun x y hy => by simp⟩
    refine hv0 (((l1 _ h3).2 ?_).trans (zero_smul ℂ v))
    rw [l2, h2, zero_smul]
  · intro y y' hy hy' f f' κ κ' hf hf' rf rf' μ 𝓕 hμ
    have e := (hT y hy f _ rf.1).1 ⟨hf, rf⟩
    have e' := (hT y' hy' f' _ rf'.1).1 ⟨hf', rf'⟩
    rw [(GlobalTheory.Ker.Ctx.th_laws D V W C _ (hd y hy) v hv).2.1] at e
    rw [(GlobalTheory.Ker.Ctx.th_laws D V W C _ (hd y' hy') v hv).2.1] at e'
    have h1 := ipO_Th C hμ (hd y hy) (hd y' hy') hv hv
    refine Eq.trans ?_ (congrArg (κ * conj κ' * ·) h1)
    rw [e, e', GlobalTheory.Ker.ipO, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAEMulMem
section
open scoped TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralAdeleProducts

theorem intAf_mul {F : Type} [Field F] [NumberField F] {a b : FiniteAdeleRing (𝓞 F) F}
    (ha : a ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F) (hb : b ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F) : a * b ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F :=
  fun v => mul_mem (ha v) (hb v)

theorem intAE_mul_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {s t : FiniteAdeleRing (𝓞 F) F ⊗[F] E}
    (hs : s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) (ht : t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) :
    s * t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  unfold HeckeCharacterZeroLocus.ThmBIn.intAE at hs ht
  induction hs using AddSubgroup.closure_induction with
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  | mem x hx =>
    obtain ⟨a, ha, p, rfl⟩ := hx
    induction ht using AddSubgroup.closure_induction with
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
    | mem y hy =>
      obtain ⟨b, hb, q, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, intAf_mul ha hb, p * q, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl

end GlobalTheory.IntegralAdeleProducts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.HeckeExtend

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F) in
def intF (N : ℕ) : Set (AF F) :=
  {x | ∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ x.2 = N • c}

theorem intF_one_mul {x y : AF F} (hx : x ∈ intF F 1) (hy : y ∈ intF F 1) : x * y ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  obtain ⟨d, hd, e'⟩ := hy
  refine ⟨c * d, fun v => mul_mem (hc v) (hd v), ?_⟩
  rw [one_smul] at e e' ⊢
  show x.2 * y.2 = c * d
  rw [e, e']


variable (F E) in
def SE : AddSubgroup (AF F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ s ∈ intF F 1, ∃ o : 𝓞 E, z = algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o}

theorem gen_mul {x y : AF F ⊗[F] E}
    (hx : x ∈ {z | ∃ s ∈ intF F 1, ∃ o : 𝓞 E, z = algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o})
    (hy : y ∈ {z | ∃ s ∈ intF F 1, ∃ o : 𝓞 E, z = algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o}) :
    x * y ∈ SE F E := by
  obtain ⟨s, hs, o, rfl⟩ := hx
  obtain ⟨s', hs', o', rfl⟩ := hy
  refine AddSubgroup.subset_closure ⟨s * s', intF_one_mul hs hs', o * o', ?_⟩
  have h : ((o * o' : 𝓞 E) : E) = (o : E) * o' := rfl
  rw [map_mul, h, map_mul]
  ring

theorem SE_mul {x y : AF F ⊗[F] E} (hx : x ∈ SE F E) (hy : y ∈ SE F E) : x * y ∈ SE F E := by
  induction hx using AddSubgroup.closure_induction with
  | mem g hg =>
    induction hy using AddSubgroup.closure_induction with
    | mem g' hg' => exact gen_mul hg hg'
    | zero => rw [mul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | neg a _ ha => rw [mul_neg]; exact neg_mem ha
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_mul]; exact neg_mem ha

theorem one_mem_SE : (1 : AF F ⊗[F] E) ∈ SE F E :=
  AddSubgroup.subset_closure ⟨1, ⟨1, fun v => one_mem _, by rw [one_smul]; rfl⟩, 1, by simp [Algebra.TensorProduct.one_def]⟩


variable (F E) in
def CE (N : ℕ) : AddSubgroup (AF F ⊗[F] E) := (SE F E).map (nsmulAddMonoidHom N)

theorem mem_CE {N : ℕ} {z : AF F ⊗[F] E} : z ∈ CE F E N ↔ ∃ s ∈ SE F E, N • s = z := by
  simp [CE]

theorem CE_step {N : ℕ} {x y : AF F ⊗[F] E} (hx : x - 1 ∈ CE F E N) (hy : y - 1 ∈ CE F E N) :
    x * y - 1 ∈ CE F E N := by
  obtain ⟨a, ha, ea⟩ := mem_CE.1 hx
  obtain ⟨b, hb, eb⟩ := mem_CE.1 hy
  refine mem_CE.2 ⟨a + b + N • (a * b), add_mem (add_mem ha hb) (nsmul_mem (SE_mul ha hb) N), ?_⟩
  rw [eq_add_of_sub_eq ea.symm, eq_add_of_sub_eq eb.symm]
  simp only [nsmul_eq_mul]
  ring


variable (F E) in
def WE (N : ℕ) : Subgroup (AF F ⊗[F] E)ˣ where
  carrier := {z | (z : AF F ⊗[F] E) - 1 ∈ CE F E N ∧ ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 ∈ CE F E N}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => ⟨by rw [Units.val_mul]; exact CE_step hx.1 hy.1,
    by rw [mul_inv_rev, Units.val_mul]; exact CE_step hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem cA_gen (σ : E →ₐ[F] E) (s : AF F) (o : 𝓞 E) :
    cA σ (algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o) =
      algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E (σ o) := by
  rw [map_mul, AlgHom.commutes]
  rfl

theorem cA_mem_SE (σ : E →ₐ[F] E) {z : AF F ⊗[F] E} (hz : z ∈ SE F E) : cA σ z ∈ SE F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, hs, o, rfl⟩ := hg
    rw [cA_gen]
    have : IsIntegral ℤ (σ (o : E)) := (o.2.map σ)
    exact AddSubgroup.subset_closure ⟨s, hs, ⟨σ o, this⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end GlobalTheory.HeckeExtend

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjugationStableStructure
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
open IsDedekindDomain

namespace GlobalTheory.FinClsLoc

theorem ratInt_eventually (x : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le ?_
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

theorem ratInt_eventually_away {p : ℕ} (x : ℚ) :
    ∀ᶠ w : AwayP p in Filter.cofinite,
      algebraMap ℚ (w.1.adicCompletion ℚ) x ∈ w.1.adicCompletionIntegers ℚ :=
  (Subtype.val_injective.tendsto_cofinite).eventually (ratInt_eventually x)

section

variable {C : Type} [Ring C] [Algebra ℚ C] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ C)
  (v : HeightOneSpectrum ℤ)

theorem repr_tmul_apply' (a : v.adicCompletion ℚ) (x : C) (k : κ) :
    (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr (a ⊗ₜ[ℚ] x) k =
      a * algebraMap ℚ (v.adicCompletion ℚ) (b.repr x k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]

theorem eq_sum_tmul' (y : v.adicCompletion ℚ ⊗[ℚ] C) :
    y = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ⊗ₜ[ℚ] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end

theorem intC_stab : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), ∀ᶠ w : AwayP p in Filter.cofinite,
    (∀ a b : (w.1.adicCompletion ℚ ⊗[ℚ] G.C), IntC G w a → IntC G w b → IntC G w (a * b)) ∧
    (∀ a : (w.1.adicCompletion ℚ ⊗[ℚ] G.C), IntC G w a → IntC G w (starT G.star (w.1.adicCompletion ℚ) a).unop) ∧
    IntC G w (inC G (w.1.adicCompletion ℚ) (β : G.C)) ∧ IntC G w (inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β
  set bb := Module.finBasis ℚ G.C
  have hc : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C) ×
      Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (bb t.1 * bb t.2.1) t.2.2) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ratInt_eventually_away _
  have hs : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (G.star (bb t.1)).unop t.2) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ratInt_eventually_away _
  have hb : ∀ x : G.C, ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈ w.1.adicCompletionIntegers ℚ :=
    fun x => Filter.eventually_all.2 fun k => ratInt_eventually_away _
  have hin : ∀ (w : AwayP p) (x : G.C), (∀ k, algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈
      w.1.adicCompletionIntegers ℚ) → IntC G w (inC G (w.1.adicCompletion ℚ) x) := by
    intro w x hx k
    change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr ((1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] x) k ∈ _
    rw [repr_tmul_apply', one_mul]
    exact hx k
  filter_upwards [hc, hs, hb (β : G.C), hb ((β⁻¹ : G.Cˣ) : G.C)] with w hcv hsv hbv hbv'
  refine ⟨fun y z hy hz k => ?_, fun y hy k => ?_, hin w _ hbv, hin w _ hbv'⟩
  · change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr (y * z) k ∈ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul' bb w.1 y, eq_sum_tmul' bb w.1 z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply']
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · have hu : ∀ (f : Fin (Module.finrank ℚ G.C) → (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ᵐᵒᵖ),
        (∑ i, f i).unop = ∑ i, (f i).unop :=
      fun f => map_sum (MulOpposite.opAddEquiv : w.1.adicCompletion ℚ ⊗[ℚ] G.C ≃+ _).symm f Finset.univ
    change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr _ k ∈ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul' bb w.1 y, map_sum, hu, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    rw [starT_tmul, repr_tmul_apply']
    exact mul_mem (hy i) (hsv (i, k))

end GlobalTheory.FinClsLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceComapInjectiveIntert
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem unitOn_comap_locU (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M) (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M')
    (f : M →ₗ[ℂ] M') (hf : Function.Injective f) (hF : ∀ a b, s a = s b → ∀ x, f (F a b x) = F' a b (f x)) :
    (∀ U' : Submodule ℂ M', UnitOn s F' U' → UnitOn s F (U'.comap f)) ∧ (LocU s F' → LocU s F) := by
  have key : ∀ U' : Submodule ℂ M', UnitOn s F' U' → UnitOn s F (U'.comap f) := by
    rintro U' ⟨hfin, hst, ip', hs, hp, hadj⟩
    refine ⟨?_, ?_, ?_⟩
    · have hinj : Function.Injective (f.restrict (p := U'.comap f) (q := U') (fun x hx => hx)) := by
        intro x y hxy
        apply Subtype.ext
        apply hf
        have := congrArg Subtype.val hxy
        simpa using this
      exact Module.Finite.of_injective _ hinj
    · intro a b hab u hu
      show f (F a b u) ∈ U'
      rw [hF a b hab]
      exact hst a b hab (f u) hu
    · refine ⟨(ip'.comp f).compl₂ f, ?_, ?_, ?_⟩
      · intro x hx y hy
        simpa using hs (f x) hx (f y) hy
      · intro x hx hx0
        have : f x ≠ 0 := fun h => hx0 (hf (by rw [h, map_zero]))
        simpa using hp (f x) hx this
      · intro a b hab x hx y hy
        have hba : s b = s a := hab.symm
        simp only [LinearMap.compl₂_apply, LinearMap.comp_apply]
        rw [hF a b hab, hF b a hba]
        exact hadj a b hab (f x) hx (f y) hy
  refine ⟨key, ?_⟩
  intro hL t
  classical
  obtain ⟨U', ht, hU'⟩ := hL (t.image f)
  refine ⟨U'.comap f, ?_, key U' hU'⟩
  intro x hx
  exact ht (f x) (Finset.mem_image_of_mem f hx)

end GlobalTheory.HoweR
end

