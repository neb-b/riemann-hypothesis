module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensor

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerInductionLaw
section
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EisCont

variable {D : D7}

theorem mem_stab_onX_of_mul {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {p : GA D T} {b : GL (Fin r) (AE D)}
    (h : mt T p ⬝ d.jX = d.jX ⬝ b.1) : ∃ hp : p ∈ stab d, onX d ⟨p, hp⟩ = b :=
  ⟨⟨b, h⟩, Units.ext ((eq_of_mul_jX d (mul_jX d ⟨p, ⟨b, h⟩⟩)).trans (eq_of_mul_jX d h).symm)⟩

theorem parFlag_zero_eq_stab {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) :
    (parFlag D.sp.cm.sig T.gram d.e fun _ => 0) = stab d := by
  ext p
  constructor
  · rintro ⟨⟨B, -, hB⟩, B', -, hB'⟩
    change mt T p ⬝ d.jX = d.jX ⬝ B at hB
    change mt T p⁻¹ ⬝ d.jX = d.jX ⬝ B' at hB'
    have e1 : B ⬝ B' = 1 := by
      rw [eq_of_mul_jX d hB]
      simp only [Matrix.mul_assoc]
      rw [← hB', ← Matrix.mul_assoc (mt T p), mt_mul_inv, Matrix.one_mul, d.pX_jX]
    have e2 : B' ⬝ B = 1 := by
      rw [eq_of_mul_jX d hB']
      simp only [Matrix.mul_assoc]
      rw [← hB, ← Matrix.mul_assoc (mt T p⁻¹), mt_inv_mul, Matrix.one_mul, d.pX_jX]
    exact ⟨⟨B, B', e1, e2⟩, hB⟩
  · intro hp
    obtain ⟨α, h⟩ := hp
    obtain ⟨β, h'⟩ := (stab d).inv_mem (show p ∈ stab d from ⟨α, h⟩)
    exact ⟨⟨α.1, fun i j hij => absurd hij (lt_irrefl _), h⟩, β.1, fun i j hij => absurd hij (lt_irrefl _), h'⟩

theorem det_onX_rat {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : stab d) (hq : (q : GA D T) ∈ GQ T) :
    ∃ u : D.host.Eˣ, Units.map (incA D : D.host.E →* AE D) u =
      Matrix.GeneralLinearGroup.det (onX d q) := by
  have hr : ∀ q : stab d, (q : GA D T) ∈ GQ T → (onX d q).1 ∈ ratMx D r r := fun q hq => by
    rw [eq_of_mul_jX d (mul_jX d q)]
    exact ratMx_mul ⟨_, rfl⟩ (ratMx_mul ((mem_GQ_iff T _).1 hq) ⟨_, rfl⟩)
  obtain ⟨A, hA⟩ := hr q hq
  obtain ⟨A', hA'⟩ := hr q⁻¹ ((GQ T).inv_mem hq)
  change rat A = _ at hA
  change rat A' = _ at hA'
  have hAA : A * A' = 1 := by
    apply rat_injective
    rw [rat_mul, rat_one, hA, hA', map_inv, Units.mul_inv]
  have hA'A : A' * A = 1 := by
    apply rat_injective
    rw [rat_mul, rat_one, hA, hA', map_inv, Units.inv_mul]
  refine ⟨⟨A.det, A'.det, by rw [← Matrix.det_mul, hAA, Matrix.det_one], by rw [← Matrix.det_mul, hA'A, Matrix.det_one]⟩,
    Units.ext ?_⟩
  change incA D A.det = (onX d q).1.det
  rw [← hA, RingHom.map_det]
  rfl

theorem indLaw_inv {T T₀ : HSp D} {r : ℕ} {d : HypDec T T₀ r} {μ : (AE D)ˣ →* Circle} {t : ℂ} {φ : GA D T → ℂ}
    (hφ : IndLaw (absDet d) (detChar d μ) t φ) (q : stab d) (h1 : detChar d μ q = 1) (h2 : absDet d q = 1) (g : GA D T) :
    φ (q * g) = φ g := by
  rw [hφ q g, h1, h2]
  simp [npow]

theorem leftInv_leftGrp_of_indLaw {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {μ : (AE D)ˣ →* Circle}
    (hμ : IsHeckeChar D μ) {t : ℂ} {φ : GA D T → ℂ} (hφ : IndLaw (absDet d) (detChar d μ) t φ) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (leftGrp D.sp.cm.sig T.gram d.e fun _ => 0) φ := by
  let H : Subgroup (GA D T) :=
    { carrier := {γ | ∀ g, φ (γ * g) = φ g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {a b} ha hb g => by rw [mul_assoc, ha, hb]
      inv_mem' := fun {a} ha g => by rw [← ha, mul_inv_cancel_left] }
  have hH : (leftGrp D.sp.cm.sig T.gram d.e fun _ => 0) ≤ H := by
    refine sup_le ((Subgroup.closure_le _).2 fun u hu => ?_) fun γ hγ => ?_
    · obtain ⟨A, hA, e⟩ := lower_iff.1 hu.1
      rw [show A = 0 from Matrix.ext fun j i => hA j i le_rfl, Matrix.mul_zero, Matrix.sub_mul, Matrix.one_mul,
        sub_eq_zero] at e
      obtain ⟨hp, h1⟩ := mem_stab_onX_of_mul d (p := u) (b := 1) (e.trans (Matrix.mul_one _).symm)
      refine indLaw_inv hφ ⟨u, hp⟩ ?_ ?_
      · rw [detChar, MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one, map_one]
      · rw [absDet, MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one, map_one]
    · have hp : γ ∈ stab d := parFlag_zero_eq_stab d ▸ hγ.2
      obtain ⟨u, hu⟩ := det_onX_rat d ⟨γ, hp⟩ hγ.1
      refine indLaw_inv hφ ⟨γ, hp⟩ ?_ ?_
      · rw [detChar, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hu]
        exact hμ.2 u
      · rw [absDet, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hu]
        exact absE_inclR u
  exact fun γ hγ => hH hγ

theorem parFlag_stab_leftInv : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r), (parFlag D.sp.cm.sig T.gram d.e fun _ => 0) = stab d ∧ ratPts D.sp.cm.sig T.gram = GQ T ∧ (∀ (p : GA D T) (b : GL (Fin r) (AE D)), (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram p).1 * adMat D.host.F d.e = adMat D.host.F d.e * b.1 → ∃ hp : p ∈ stab d, onX d ⟨p, hp⟩ = b) ∧ ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (t : ℂ) (φ : GA D T → ℂ), IndLaw (absDet d) (detChar d μ) t φ → GlobalTheory.AutomorphicL2Unitary.LeftInv (leftGrp D.sp.cm.sig T.gram d.e fun _ => 0) φ :=
  fun _ _ _ _ d => ⟨parFlag_zero_eq_stab d, rfl, fun _ _ h => mem_stab_onX_of_mul d h,
    fun _ hμ _ _ hφ => leftInv_leftGrp_of_indLaw d hμ hφ⟩

end GlobalTheory.EisCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainEigenPartHasHeckeParameters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem val_hecke_of_mem_partFull {D : D7} {c : Com D} {s : PiLocalization₂ D} (u : s.CC c)
    (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (hu : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D s.V))
    (hR : Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R) (v : SmT s.M) :
    heckeLin s.V R (PiLocalization₂.val u v) = e P d • PiLocalization₂.val u v := by
  have h := ((mem_partFull c.θ s.M _ _ c.S e _).1 hu).2 P d R hR
  have key : heckeLin s.V R ∘ₗ (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = e P d • (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := by
    apply PiTensorProduct.ext
    ext x
    have := h x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply] at this ⊢
    convert congrFun this _ using 2 <;> simp [PiTensorProduct.lift_symm]
  exact congrFun (congrArg DFunLike.coe key) v |>.trans rfl

theorem partPar : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => ∀ (u : s.CC c)
    (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ),
    PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e →
    (u ≠ 0 → ∃ B, IsPar u B) ∧ ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
  intro hP D c hc j hj s hs u e hu
  obtain ⟨hval, hHk, hconj⟩ := _root_.GlobalTheory.ConjVal.conj_values_hecke hP D c hc j hj s hs
  obtain ⟨-, hlat⟩ := _root_.GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat D c hc j hj s hs
  obtain ⟨-, hsph, -⟩ := _root_.GlobalTheory.ChainOntoSph.level_spherical_off_S D c hc j hj s hs
  have hlev : ∀ v, ∀ k ∈ levS s.V s.β s.L, ∀ g, (fun g => conj (PiLocalization₂.val u v g)) (g * k) =
      (fun k => conj (Lev.levChi s.V s.β s.L k)) k * (fun g => conj (PiLocalization₂.val u v g)) g := by
    intro v k hk g
    simp only [(hval u v).2.2.2 k hk g, map_mul]
  have hhk : ∀ v P d R, Hecke₂ s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S P d R →
      heckeLin s.V R (fun g => conj (PiLocalization₂.val u v g)) = (fun P d => conj (e P d)) P d • (fun g => conj (PiLocalization₂.val u v g)) := by
    intro v P d R hR
    rw [hconj, val_hecke_of_mem_partFull u e hu P d R ((hHk P d R).2 hR) v]
    funext g
    simp [map_mul]
  have hne : ∀ v, PiLocalization₂.val u v ≠ 0 → (fun g => conj (PiLocalization₂.val u v g)) ≠ 0 := by
    intro v h0 h
    apply h0
    funext g
    simpa using congrFun h g
  have hiff : ∀ v B, PiLocalization₂.val u v ≠ 0 →
      (ParFun c s (PiLocalization₂.val u v) B ↔ GlobalTheory.LFun.IsSysParamD D c.S s.V.rank (fun P d => conj (e P d)) B) := by
    intro v B h0
    unfold ParFun
    rw [hlat]
    exact GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph (hne v h0) (hlev v) (hhk v) B
  have second : ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
    intro w B hw hB
    refine ⟨?_, fun v hv => (hiff v B hv).2 ((hiff w B hw).1 hB)⟩
    rintro rfl
    exact hw (by simp [PiLocalization₂.val])
  refine ⟨fun hu0 => ?_, second⟩
  have hu1 : (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ≠ 0 := fun h => hu0 (Subtype.ext h)
  obtain ⟨v, hv⟩ : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hu1 (LinearMap.ext hh)
  obtain ⟨C, hC⟩ := (hval u v).2.1
  have hbdd : (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj.comp (hval u v).1), fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [(hval u v).2.2.1 γ hγ g]
    · simpa using hC g
  obtain ⟨B, hB, -⟩ := _root_.GlobalTheory.FinZeta.ParamBound.exists_param_bounded D s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S hsph
    _ hbdd (hne v hv) (hlev v) (fun P d => conj (e P d)) (hhk v)
  have hpf : ParFun c s (PiLocalization₂.val u v) B := by
    unfold ParFun
    rw [hlat]
    exact hB
  exact ⟨B, second v B hv hpf⟩

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamsTrivialBoundRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ChainOnto.parBound_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LevFacts D → ParBound D := by
  intro hCRD D _hLF c hc j hj s hs u B hB
  obtain ⟨hu0, hpar⟩ := hB
  have hex : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  set f : GA D s.V → ℂ := fun g => conj (PiLocalization₂.val u v g) with hfdef
  have hPF : ParFun c s (PiLocalization₂.val u v) B := hpar v hv
  have h3 : GlobalTheory.LFun.IsParamFunV s.V c.S f B := ((_root_.GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat D c hc j hj s hs).2 f B).1 hPF
  obtain ⟨h4a, _, _⟩ := _root_.GlobalTheory.ConjVal.conj_values_hecke hCRD D c hc j hj s hs
  obtain ⟨hcont, ⟨C, hC⟩, hinv, hlev⟩ := h4a u v
  obtain ⟨_, hsph, _⟩ := _root_.GlobalTheory.ChainOntoSph.level_spherical_off_S D c hc j hj s hs
  have hfmem : f ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [hfdef, hinv γ hγ g]
    · simpa [hfdef] using hC g
  have hf0 : f ≠ 0 := by
    intro h0
    apply hv
    funext g
    have := congrFun h0 g
    simpa [hfdef] using this
  have hlev' : ∀ k ∈ levS s.V s.β s.L, ∀ g, f (g * k) = conj (Lev.levChi s.V s.β s.L k) * f g := by
    intro k hk g
    simp only [hfdef, hlev k hk g, map_mul]
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.ParamEigen.eig_of_param D s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S hsph B
  obtain ⟨B', hB', hbd⟩ := _root_.GlobalTheory.FinZeta.ParamBound.exists_param_bounded D s.V _ _ c.S hsph f hfmem hf0 hlev' a (fun P d R hR => ha f h3 P d R hR)
  intro w hw
  rw [GlobalTheory.LFun.IsParamVecOff.unique h3 hB' hw]
  exact hbd w hw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainMetric

theorem integ_pair {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    {X : Type} [MeasurableSpace X] {μ : Measure X} {A : Set X}
    (f g : (⨂[ℂ] i, E i) →ₗ[ℂ] (X → ℂ)) (B : (⨂[ℂ] i, E i) →ₗ[ℂ] (⨂[ℂ] i, E i) →ₗ⋆[ℂ] ℂ) (k : ℂ)
    (h : ∀ v v' : ∀ i, E i, IntegrableOn (fun x => f (PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x)) A μ ∧
      ∫ x in A, f (PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x) ∂μ =
        k * B (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v')) :
    ∀ w w', IntegrableOn (fun x => f w x * conj (g w' x)) A μ ∧ ∫ x in A, f w x * conj (g w' x) ∂μ = k * B w w' := by

  have left : ∀ (w : ⨂[ℂ] i, E i) (v' : ∀ i, E i),
      IntegrableOn (fun x => f w x * conj (g (PiTensorProduct.tprod ℂ v') x)) A μ ∧
        ∫ x in A, f w x * conj (g (PiTensorProduct.tprod ℂ v') x) ∂μ = k * B w (PiTensorProduct.tprod ℂ v') := by
    intro w v'
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      obtain ⟨h1, h2⟩ := h v v'
      have e : (fun x => f (r • PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x)) =
          fun x => r * (f (PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x)) := by
        funext x
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact Integrable.const_mul h1 r
      · rw [e, integral_const_mul, h2]
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
    | add a b ha hb =>
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      have e : (fun x => f (a + b) x * conj (g (PiTensorProduct.tprod ℂ v') x)) =
          fun x => f a x * conj (g (PiTensorProduct.tprod ℂ v') x) + f b x * conj (g (PiTensorProduct.tprod ℂ v') x) := by
        funext x
        simp only [map_add (f := _), Pi.add_apply, add_mul]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact Integrable.add ha1 hb1
      · rw [e, integral_add ha1 hb1, ha2, hb2]
        simp only [map_add (f := _), LinearMap.add_apply, mul_add]

  intro w w'
  induction w' using PiTensorProduct.induction_on with
  | smul_tprod r v' =>
    obtain ⟨h1, h2⟩ := left w v'
    have e : (fun x => f w x * conj (g (r • PiTensorProduct.tprod ℂ v') x)) =
        fun x => conj r * (f w x * conj (g (PiTensorProduct.tprod ℂ v') x)) := by
      funext x
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      ring
    refine ⟨?_, ?_⟩
    · rw [e]
      exact Integrable.const_mul h1 (conj r)
    · rw [e, integral_const_mul, h2]
      simp only [LinearMap.map_smulₛₗ, smul_eq_mul]
      ring
  | add a b ha hb =>
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    have e : (fun x => f w x * conj (g (a + b) x)) =
        fun x => f w x * conj (g a x) + f w x * conj (g b x) := by
      funext x
      simp only [map_add (f := _), Pi.add_apply, mul_add]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact Integrable.add ha1 hb1
    · rw [e, integral_add ha1 hb1, ha2, hb2]
      simp only [map_add (f := _), mul_add]

variable {D : D7}

theorem val_tprod {V' : HSp D} {S' : D.what₂.Tau → SPar} {M' : DSModel V' S'} (x : (⨂[ℂ] τ, M'.sm τ) →ₗ[ℂ] (GA D V' → ℂ))
    (v : M'.Vec) : x (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm x v := by
  rw [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply]

theorem metEx : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  intro hP D c hc j _ s hs
  obtain ⟨ipD, hpure, hhermD, hposD⟩ := _root_.GlobalTheory.ChainOnto.exists_ipD_smT D s.V s.par s.M
  have hθ : IsInfFam c.θ := hc.inf
  have hμ := hs.haar
  have h𝓕 := hs.fund
  have hSM : SchurMult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) s.ν s.fd :=
    GlobalTheory.MultFinite.schurMult hP s.ν s.fd
  have hmem : ∀ x : s.CC c, PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) :=
    fun x => (mem_multT c.θ s.M _ _ _).1 x.2
  by_cases hsm : ∀ τ, s.M.sm τ ≠ ⊥
  ·
    obtain ⟨hlin, hpos⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M _ _ s.ν s.fd hθ hμ h𝓕 hSM hsm
    have hherm : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
        ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
          ipM s.M s.ν s.fd T' T = star (ipM s.M s.ν s.fd T T') :=
      fun T hT T' hT' => (hlin T hT T' hT' T' hT' 0).2
    have hadd : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
        ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
          ∀ T'' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
            ipM s.M s.ν s.fd T (T' + T'') = ipM s.M s.ν s.fd T T' + ipM s.M s.ν s.fd T T'' := by
      intro T hT T' hT' T'' hT''
      have := (hlin T hT T' hT' T'' hT'' 1).1
      rwa [one_smul, one_mul] at this
    have hzero : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L), ipM s.M s.ν s.fd T 0 = 0 := by
      intro T hT
      have := hadd T hT 0 (zero_mem _) 0 (zero_mem _)
      rw [add_zero] at this
      linear_combination -this
    have hsmul : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
        ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L), ∀ a : ℂ,
          ipM s.M s.ν s.fd T (a • T') = a * ipM s.M s.ν s.fd T T' := by
      intro T hT T' hT' a
      have := (hlin T hT 0 (zero_mem _) T' hT' a).1
      rwa [zero_add, hzero T hT, zero_add] at this

    have hIP : ∀ x y : s.CC c, ∀ w w',
        IntegrableOn (fun g => (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w g *
          conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w' g)) s.fd s.ν ∧
        ∫ g in s.fd, (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w g * conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w' g) ∂s.ν =
          ipM s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
            (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))) * ipD w w' := by
      intro x y
      apply integ_pair
      intro v v'
      have hex := hSM hθ hμ h𝓕 _ (hmem y) _ (hmem x)
      have hc : IsMultIP s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
          (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
          (ipM s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
            (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) := by
        rw [ipM, dite_eq_left hex]
        exact hex.choose_spec
      obtain ⟨h1, h2⟩ := hc v' v
      have e : (fun g => (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v) g *
          conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v') g)) =
          fun g => star (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v' g) *
            PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v g := by
        funext g
        rw [val_tprod, val_tprod, mul_comm, starRingEnd_apply]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact h1
      · rw [e, h2, hpure]
    refine ⟨ipD, LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun x y : s.CC c => ipM s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
        (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) ?_ ?_ ?_ ?_, ?_⟩
    · intro x x' y
      simp only [Submodule.coe_add, map_add (f := _)]
      exact hadd _ (hmem y) _ (hmem x) _ (hmem x')
    · intro a x y
      simp only [Submodule.coe_smul, map_smul, RingHom.id_apply, smul_eq_mul]
      exact hsmul _ (hmem y) _ (hmem x) a
    · intro x y y'
      simp only [Submodule.coe_add, map_add (f := _)]
      rw [hherm _ (hmem x) _ (add_mem (hmem y) (hmem y')), hadd _ (hmem x) _ (hmem y) _ (hmem y'), star_add,
        ← hherm _ (hmem x) _ (hmem y), ← hherm _ (hmem x) _ (hmem y')]
    · intro a x y
      simp only [Submodule.coe_smul, map_smul, smul_eq_mul]
      rw [hherm _ (hmem x) _ (Submodule.smul_mem _ a (hmem y)), hsmul _ (hmem x) _ (hmem y), star_mul',
        ← hherm _ (hmem x) _ (hmem y), starRingEnd_apply]
    · refine ⟨hpure, hhermD, hposD, ?_, ?_, ?_, ?_⟩
      · intro x y
        simp only [LinearMap.mk₂'ₛₗ_apply]
        rw [hherm _ (hmem x) _ (hmem y), starRingEnd_apply]
      · intro x hx
        simp only [LinearMap.mk₂'ₛₗ_apply]
        refine hpos _ (hmem x) fun h0 => hx ?_
        apply Subtype.ext
        rw [Submodule.coe_zero]
        exact (LinearEquiv.map_eq_zero_iff _).1 h0
      · intro x y w w'
        exact (hIP x y w w').1
      · intro x y w w'
        simp only [Lift.pet, LinearMap.mk₂'ₛₗ_apply]
        exact (hIP x y w w').2
  ·
    push_neg at hsm
    obtain ⟨τ₀, hτ₀⟩ := hsm
    have htp : ∀ v : s.M.Vec, PiTensorProduct.tprod ℂ v = 0 := by
      intro v
      apply (PiTensorProduct.tprod ℂ).map_coord_zero τ₀
      have : (v τ₀ : s.M.H τ₀) ∈ (⊥ : Submodule ℂ (s.M.H τ₀)) := hτ₀ ▸ (v τ₀).2
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
    have hz : ∀ w : SmT s.M, w = 0 := by
      intro w
      induction w using PiTensorProduct.induction_on with
      | smul_tprod r v => rw [htp v, smul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    refine ⟨ipD, 0, hpure, hhermD, hposD, ?_, ?_, ?_, ?_⟩
    · intro x y
      simp
    · intro x hx
      exfalso
      apply hx
      apply Subtype.ext
      apply LinearMap.ext
      intro w
      rw [hz w]
      simp
    · intro x y w w'
      rw [hz w, hz w']
      simp
    · intro x y w w'
      rw [hz w, hz w']
      simp [Lift.pet]

end GlobalTheory.ChainMetric
end
end

