module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0814
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeEltAll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HalfTranslatesLeLevelHalfTranslatesOfDvd
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem trSp_le_of_subhalf : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (e₂ e' : AE D) (P' : Finset (Formalism.L2.DIV.Pl D.host.E)), IsHalfIdem l₂ e₂ → IsIdemSum e' P' → (∀ PP ∈ P', l₂.Mb ≤ PP.asIdeal) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (f₀ : WO V W → ℂ) (M : ℕ) (O : Subring ℂ), trSp ψ V W ΛV ΛW f₀ e' M O ≤ trSp ψ V W ΛV ΛW f₀ e₂ M O := by
  intro D H l₂ e₂ e' P' h₂ h' hP ψ V W ΛV ΛW f₀ M O
  obtain ⟨P₂, ⟨⟨es₂, hes₂, rfl⟩, -⟩, hP₂⟩ := h₂
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  have hsub : P' ⊆ P₂ := fun PP h => (hP₂ PP).2 (hP PP h)
  have key := GlobalTheory.PartialIdemSum.sum_mul_sum_of_subset P' P₂ es' es₂ hes' hes₂ hsub
  unfold trSp
  refine Submodule.span_mono ?_
  rintro f ⟨y, hy, hM, rfl⟩
  refine ⟨y, fun i j => ?_, hM, rfl⟩
  rw [← hy i j, ← mul_assoc, mul_comm (∑ P ∈ P₂, es₂ P), key]

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmVecEqPhaseLetters
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SerLetters

theorem coord_mem_fieldRange {ι K J : Type} [Field K] [Fintype J] (σ : K →+* ℂ) (e : J → MvPolynomial ι K)
    (hli : LinearIndependent ℂ fun j => MvPolynomial.map σ (e j)) (a : J → ℂ)
    (hx : ∀ m, AddMonoidAlgebra.coeff (∑ j, a j • MvPolynomial.map σ (e j)) m ∈ σ.fieldRange) (j : J) :
    a j ∈ σ.fieldRange := by
  classical
  by_contra hj
  letI : Algebra K ℂ := σ.toAlgebra
  let p : Submodule K ℂ := LinearMap.range (Algebra.linearMap K ℂ)
  have hp : ∀ z ∈ σ.fieldRange, z ∈ p := fun z hz => by
    obtain ⟨y, rfl⟩ := RingHom.mem_fieldRange.1 hz
    exact ⟨y, rfl⟩
  have hnot : a j ∉ p := fun h => hj (by obtain ⟨y, hy⟩ := h; exact RingHom.mem_fieldRange.2 ⟨y, hy⟩)
  obtain ⟨π, hπ, hπp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hπ0 : ∀ z ∈ p, π z = 0 := fun z hz => by
    have : π z ∈ p.map π := Submodule.mem_map_of_mem hz
    rwa [hπp, Submodule.mem_bot] at this
  have hsum : ∑ k, π (a k) • e k = 0 := by
    ext m
    have h1 := hπ0 _ (hp _ (hx m))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, map_sum] at h1
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_zero]
    change (∑ x, π (a x) * (e x).coeff m) = 0
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : a k * σ (AddMonoidAlgebra.coeff (e k) m) = AddMonoidAlgebra.coeff (e k) m • a k := by
      rw [Algebra.smul_def]; exact mul_comm _ _
    rw [e1, map_smul, smul_eq_mul, mul_comm]
  have h2 : ∑ k, σ (π (a k)) • MvPolynomial.map σ (e k) = 0 := by
    have := congrArg (MvPolynomial.map σ) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, MvPolynomial.smul_eq_C_mul, MvPolynomial.map_C] using this
  have h3 := Fintype.linearIndependent_iff.1 hli _ h2 j
  exact hπ ((map_eq_zero σ).1 h3)

end GlobalTheory.SerLetters

section Letters1
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerLetters
open GlobalTheory.AdTh.PhaseMap GlobalTheory.AdTh.PhaseMapFree


set_option maxHeartbeats 1600000 in
theorem io_eq_phase_smul_letters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ i : Fin D.R.m, VStd D i → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank, GlobalTheory.AdTh.PhaseMap.IsLt lt → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∃ io : VsV D i T.Q.c.F →ₗ[T.Q.c.F] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F, (∀ v, io v ∈ Submodule.span T.Q.c.F (HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank T.Q.c.F ComplexEmbedding.conjugate (InPsi T.Q.H) (fun τ j => wtA (κ i) (τ, j)))) ∧ ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ v : VsV D i T.Q.c.F, pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) (c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) v))) = ka • pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) f (GlobalTheory.AdTh.PhaseMap.toF T.Q.c lt (io v)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hFam hM hP hT i hstd u hu c0 hc lt hl
  have hθ : IsInfFam R.θ := hM.inf
  have hcV : (R.cV i).Is := hM.cV i
  have hPr := isPair_of_clauses D G Pl0 T0 A _ R hL hM hP i A.μ0 hstd
  have hψ := hPr.weil.std
  obtain ⟨f1, f2, f3, f4, f5⟩ := vec_fock_of_clauses D G Pl0 T0 A _ R hM hP i A.μ0 hstd
  obtain ⟨io, hw, hio⟩ := GlobalTheory.CoefMapRecord.exists_io_record D T.Q hT.laws.pins κ hT.kap i T.Q.c
  obtain ⟨hwok, cga, i1, i2, irng, i3, -, -, i4, -⟩ := hio
  obtain ⟨n1, n2, n3, n4, hc0⟩ := _root_.GlobalTheory.AdTh.CoefC.coefMap_complex_core D G Pl0 T0 A T R κ v₀ hT i hstd c0 hc hw hwok
  obtain ⟨r1, r2, -⟩ := GlobalTheory.RatGen.rational_points_generate D (Vc D i) (R.cV i) (hM.vpos i) hPr.sigV hcV
  obtain ⟨-, -, w1, w2, w3⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hT.laws.pins _ (inR i) (κ i)
  have hty : IsTyp D T.Q.H := ⟨w1, w2⟩
  obtain ⟨d1, d2, -⟩ := hT.laws.pins.2.2.2 _ (inR i)
  have hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨u₀, w₀, hu₀, hw₀, hΔ⟩ : ExtremalVectorPairsToDelta R i (v₀ i (sg0 D A)) :=
    (hT.hv₀ i (sg0 D A)).2 rfl (GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ R hL hFam hM hP i)
  obtain rfl : u = u₀ := funext fun ρ => Subtype.ext ((hu ρ).trans (hu₀ ρ).symm)
  clear hu₀
  have hioP := (hP.ioP i A.μ0).1
  have hBV : ∀ τ, (R.BV i τ)ᴴ * R.BV i τ = 1 := fun τ => by
    obtain ⟨ε, hε, h1, -⟩ := hM.BV i τ
    rw [gramAt_one hPr.std, Matrix.mul_one] at h1
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with h | h
    · rw [h.1]; rfl
    · exact absurd a.2 (not_lt.2 h.2)
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ =>
    ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [gramAt_one hPr.std], by simp⟩
  let PTf := fun f => pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1)
    (onb (R.MW i (sg0 D A))) f
  let PT := PTf (R.vP i A.μ0)
  have hsub : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (U : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ),
      (∀ τ, (U τ)ᴴ * U τ = 1) → ∀ P,
      pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) U (onb (R.MW i (sg0 D A))) f P =
        PTf f (GlobalTheory.AdTh.PhaseMap.sub (fun τ => ((Wc D i).sig (tauE D τ)).1) U P) := fun f hf U hU P => by
    have h := GlobalTheory.AdTh.SourceBasis.pureTensorO_mul_source D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ (fun _ => 1) U _ _ _ f5
      (fun τ => (trace_parity (f5 τ)).1) (fun τ => by simp) (fun τ => det_ne_zero (hU τ)) f hf P
    simp only [Matrix.one_mul] at h
    exact h
  have hinj : Function.Injective PT :=
    GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ _ _ _ _ _ _ f4 f3 hon f5 hPr.sigV hPr.sigW _ f1 f2
      (thetaVector_ne_zero_of_clauses D G Pl0 T0 A _ R hL hP i)
  obtain ⟨g, hg, hgB⟩ : ∃ g ∈ GinfC (Vc D i), ∀ τ, compAt R.θ τ (Formalism.L2.Theta.mt (Vc D i) g) = R.BV i τ :=
    (GlobalTheory.SmoothForms.RealPts.glue R.θ hθ (Vc D i)).2 (R.BV i) fun τ => by
      show (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = gramAt D (Vc D i) τ
      rw [gramAt_one hPr.std, Matrix.mul_one, hBV]
  obtain ⟨χ, hχ, hχg⟩ := om_real hPr f4 f3 f5 f1 f2 hg
  rw [funext hgB] at hχg
  let A₀ : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
    pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i A.μ0) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)
  have hA₀ : ∀ a ∈ GinfC (Vc D i), ∀ w, A₀ ((R.cV i).ρ a w) = R.ωP i A.μ0 (a, 1) (A₀ w) :=
    fun a ha w => (hioP a ha _ w).symm
  have hw₁ : A₀ ((R.cV i).ρ g⁻¹ (χ • w₀)) = PT (RealDat.Delta i) := by
    have h1 : A₀ (χ • w₀) = R.ωP i A.μ0 (g, 1) (PT (RealDat.Delta i)) := by
      rw [map_smul, hχg, ← hΔ]
      rfl
    rw [hA₀ _ (inv_mem hg), h1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one]
    exact congrArg (fun T : Module.End ℂ _ => T _) (map_one (R.ωP i A.μ0))
  have hn₁ : ‖(R.cV i).ρ g⁻¹ (χ • w₀)‖ = 1 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hcV.2.1, ← norm_eq_sqrt_re_inner, norm_smul, hχ, hw₀, mul_one]
  haveI := hcV.2.2.2.1
  haveI : FiniteDimensional T.Q.c.F (VsV D i T.Q.c.F) := Module.Finite.of_basis (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i))
  let c0' : VsV D i T.Q.c.F →ₛₗ[inC T.Q.c] (R.cV i).W :=
    { toFun := fun v => c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) v)
      map_add' := fun v w => by
        rw [← map_add (f := _)]
        congr 1
        exact Subtype.ext (map_add (MvPolynomial.map (inC T.Q.c)) _ _)
      map_smul' := fun a v => by
        rw [← map_smul]
        congr 1
        apply Subtype.ext
        show MvPolynomial.map (inC T.Q.c) (a • (v : Pol T.Q.c.F D.what₂.Tau (Vc D i).rank)) =
          (inC T.Q.c a) • MvPolynomial.map (inC T.Q.c) (v : Pol T.Q.c.F D.what₂.Tau (Vc D i).rank)
        rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C] }
  have n1' : ‖c0' hw‖ = 1 := n1
  have n2' : ∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE → ∀ v,
      c0' (rhoM T.Q.c (fun τ => embF T.Q.c (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) v) = (R.cV i).ρ γ (c0' v) := n2
  have n3' : Submodule.span ℂ (Set.range c0') = ⊤ := n3
  have hsm : ∀ (a : T.Q.c.F) P, toF T.Q.c lt (a • P) = (a : ℂ) • toF T.Q.c lt P := fun a P => by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, toF_C, MvPolynomial.smul_eq_C_mul]
  set_option synthInstance.maxHeartbeats 200000 in
  obtain ⟨B₀, hB₀⟩ := exists_ext c0' n4
    { toFun := fun v => toF T.Q.c lt (io v)
      map_add' := fun v w => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun a v => by rw [map_smul, hsm]; rfl }
  replace hB₀ : ∀ v, B₀ (c0' v) = toF T.Q.c lt (io v) := hB₀
  have hpG : toF T.Q.c lt (io hw) = RealDat.Delta i := by
    rw [i4]
    refine toF_pG T.Q.c hl hty i1 _ _ _ _ _ (fun τ => by rw [hsig, d1]) (fun τ => by rw [hsig, d2]) (fun τ k hk => ?_)
      fun τ k hk => ?_
    · rw [d1] at hk
      exact (w3 τ k).1.trans ((dif_pos hk).trans ((hT.kap i τ).1 ⟨k, hk⟩))
    · rw [d2] at hk
      exact (w3 τ k).2.trans ((dif_pos hk).trans ((hT.kap i τ).2.1 ⟨k, hk⟩))
  have hne : PT (B₀ (c0' hw)) ≠ 0 := fun h => by
    rw [hB₀, map_eq_zero_iff _ hinj, map_eq_zero_iff _ (toF_injective T.Q.c hl hty), map_eq_zero_iff _ i2] at h
    rw [h, map_zero, norm_zero] at n1'
    exact zero_ne_one n1'
  have hwz : A₀ ((R.cV i).ρ g⁻¹ (χ • w₀)) = (PT ∘ₗ B₀) (c0' hw) := by rw [hw₁, LinearMap.comp_apply, hB₀, hpG]
  have hAeq : ∀ γ : GQ (Vc D i), ∃ s : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ),
      ∀ w, A₀ ((R.cV i).ρ γ w) = s (A₀ w) := fun γ => by
    obtain ⟨γE, a, k, h1, h2, h3, h4, h5, h6⟩ := rat_parts hθ hPr.std γ
    have h7 : (R.cV i).ρ γ = (R.cV i).ρ a := by rw [h4, map_mul, hcV.1 k h3, mul_one]
    exact ⟨R.ωP i A.μ0 (a, 1), fun w => by rw [h7, hA₀ a h2]⟩
  have hAi : Function.Injective A₀ := by
    rw [← LinearMap.ker_eq_bot]
    refine (r2 _ fun γ => ?_).resolve_right fun h => hne ?_
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨s, hs⟩ := hAeq γ
      have hx' : A₀ x = 0 := hx
      show A₀ ((R.cV i).ρ γ x) = 0
      rw [hs, hx', map_zero]
    · rw [← LinearMap.comp_apply, ← hwz]
      exact (h ▸ Submodule.mem_top : (R.cV i).ρ g⁻¹ (χ • w₀) ∈ LinearMap.ker A₀)
  obtain ⟨a, ha, ha'⟩ := proportional ((R.cV i).ρ.comp (GQ (Vc D i)).subtype) _ r1 (fun γ hγ => hγ) r2 A₀ (PT ∘ₗ B₀)
    (fun γ => by
      obtain ⟨γE, a, k, h1, h2, h3, h4, h5, h6⟩ := rat_parts hθ hPr.std γ
      obtain ⟨x, hx, hxa⟩ := om_real hPr f4 f3 f5 f1 f2 h2
      have hx0 : x ≠ 0 := fun h => by simp [h] at hx
      have h7 : (R.cV i).ρ γ = (R.cV i).ρ a := by rw [h4, map_mul, hcV.1 k h3, mul_one]
      refine ⟨R.ωP i A.μ0 (a, 1), (cga γE.val : ℂ) * x⁻¹, fun w => ?_, fun w => ?_⟩
      · show A₀ ((R.cV i).ρ γ w) = _
        rw [h7, hA₀ a h2]
      · have h8 : (PT ∘ₗ B₀) ∘ₗ (R.cV i).ρ γ =
            ((cga γE.val : ℂ) * x⁻¹) • (R.ωP i A.μ0 (a, 1) ∘ₗ (PT ∘ₗ B₀)) := by
          refine LinearMap.ext_on_range n3' fun v => ?_
          simp only [LinearMap.comp_apply, LinearMap.smul_apply]
          rw [← n2' γ γE h1, hB₀, hB₀, i3 _ h5, hsm, hxa, hsub _ f1 _ (compAt_unitary hθ hPr.std a), smul_smul,
            inv_mul_cancel_right₀ hx0, map_smul,
            toF_gaStar T.Q.c hl hty (fun τ => ((Wc D i).sig (tauE D τ)).1) (fun τ => by rw [hsig, d1]) _ _ h6]
        exact LinearMap.congr_fun h8 w)
    ((R.cV i).ρ g⁻¹ (χ • w₀)) (c0' hw) hwz hne
  have h9 : ∀ x, GlobalTheory.AdTh.PhaseMap.sub (fun τ => ((Wc D i).sig (tauE D τ)).1) (R.BV i) (R.ioP i (PiTensorProduct.tprod ℂ u) x) =
      a • B₀ x := fun x => hinj (by rw [← hsub _ f1 _ hBV, map_smul]; exact ha x)
  have hB₀i : Function.Injective B₀ := fun x y hxy => hAi (by rw [ha, ha, LinearMap.comp_apply, LinearMap.comp_apply, hxy])
  refine ⟨a, ?_, io, fun v => irng ▸ LinearMap.mem_range_self io v, fun f hf v => ?_⟩
  · rw [← n1', ← ha', norm_smul, hn₁, mul_one]
  · rw [hsub f hf _ hBV, h9, map_smul, ← hB₀ v]
    rfl

end GlobalTheory.SerLetters
end Letters1

section Letters2
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerLetters

theorem map_mem_HHa {T0 : Type} {r : T0 → ℕ} {n : ℕ} {k K : Type} [Field k] [CharZero k] [Field K] (φ : k →+* K)
    {cc : T0 → T0} {isX : T0 → Prop} {a : T0 → ℕ → ℕ} {P : MvPolynomial (Letter T0 r n) k} (h : P ∈ HHa r n k cc isX a) :
    MvPolynomial.map φ P ∈ HHa r n K cc isX a := by
  haveI : Infinite k := Infinite.of_injective (fun m : ℕ => (m : k)) Nat.cast_injective
  exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map φ h.1, ReciprocityTheory.ChartRestriction.G.PullbackSections.rowInv_map φ h.2.1, ReciprocityTheory.ChartRestriction.G.PullbackSections.rowDeg_map φ h.2.2⟩

end GlobalTheory.SerLetters
end Letters2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePreservesSupLatticeAndCommutesTypeGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem supHk_commG : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → SupHk D ∧ CommG D := by
  intro D X E Y hSup
  exact GlobalTheory.HkSupComm.supHk_commG D X.Γ X.Pl0 X.I0 X.T X.A3 X.core X.R X.cG Y.S Y.YS Y.H Y.sup X.char.lev X.char.allPl
    (fun i => (X.integral i).2.1) hSup Y.reads (fun i b P h _ => (_root_.GlobalTheory.TwUnit.isKsForm_and_unit D X E Y).2 i b P h)

end GlobalTheory.TwInputs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeReadOfDeltaFrob
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TwInputs.HeckePinRead

theorem pull_locE {D : D7} {Ω : Type} [Field Ω] [Algebra D.host.E Ω] {A : Type} [CommGroup A] (a : Recip D Ω) (ha : a.Good)
    (φ : G D.host.E Ω →* A) (hφ : IsOpen (φ.ker : Set (G D.host.E Ω))) (P : Pl D.host.E) (e : AE D)
    (he : Formalism.L2.JoinChr.IsPlIdem D e P) (k : D.host.Eˣ)
    (hk : Valued.v ((Formalism.L2.Host.atFin P k : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ))
    (x : (AE D)ˣ) (hx : (x : AE D) = Formalism.L2.JoinChr.locE D e (k : D.host.E)) (B : ValuationSubring Ω)
    (hB : IsPlaceOver (F := D.host.E) B P) (hine : ∀ τ ∈ Ine (F := D.host.E) B, φ τ = 1) (σ : G D.host.E Ω)
    (hσ : IsFrob (F := D.host.E) B (normV P) σ) : a.pull φ x = (φ σ)⁻¹ := by
  have hκ : a.κ (x : AE D) = ((Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) : Neutral.B1.Ideles D.host.E) :
      AdeleRing (𝓞 D.host.E) D.host.E) := by
    rw [hx]; exact ha.loc P e he k
  have hsym : a.sym x = a.art (Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k)) := by
    rw [Recip.sym, MonoidHom.comp_apply]
    congr 1
    exact Units.ext hκ
  obtain ⟨y, hy, hyσ⟩ := (ha.artin.frob P B hB _).mpr ⟨σ, hσ, rfl⟩
  have hu : Valued.v (((Formalism.L2.Host.atFin P k * y⁻¹ : (P.adicCompletion D.host.E)ˣ)) : P.adicCompletion D.host.E) = 1 := by
    have hy' : Valued.v ((y : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ) := hy
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hk, hy']
    exact mul_inv_cancel₀ WithZero.exp_ne_zero
  obtain ⟨τ, hτ, hτu⟩ := (ha.artin.ine P B hB _).mp ⟨_, hu, rfl⟩
  have hs : a.sym x = GlobalTheory.HeckeGal.toAb D.host.E Ω (τ * σ⁻¹) := by
    rw [hsym, show Formalism.L2.Host.atFin P k = (Formalism.L2.Host.atFin P k * y⁻¹) * y by group, map_mul, map_mul, hyσ,
      ← hτu, map_mul]
  rw [a.pull_eq hφ hs, map_mul, hine τ hτ, map_inv, one_mul]

theorem isOpen_ker_psiAt (D : D7) (i : D.ntw.Tw) (b : Bool) :
    IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
  have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
    ext g
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
  rw [e]
  exact D.ntw.delta_open i

theorem chi_locU_unif {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (P : PlE D.host)
    (hP : P ∉ D.ntw.S0 i) {e : AE D} (he : Formalism.L2.JoinChr.IsPlIdem D e P) (hee : e * e = e) (σ : G D.host.E D.nd.Om)
    (hσ : IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ) :
    (((ρ.B i j b).de.chi (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif P)) : Circle) : ℂ) =
      (ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)))⁻¹ := by
  rw [hρ.delta i j b]
  have hopen := isOpen_ker_psiAt D i b
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ⁻¹ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ⁻¹)
  have hine : ∀ τ ∈ Ine (F := D.host.E) (D.nd.plOm.1 P), Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) τ = 1 := by
    intro τ hτ
    have h : D.ntw.delta i τ = 1 := by
      by_contra hne
      exact hP (D.ntw.primes_subset_exceptional i ((D.ntw.delta_ram i P _ (D.nd.plOm.2 P)).1 ⟨τ, hτ, hne⟩))
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, h]
  have hpull := pull_locE ρ.rc hρ.rc _ hopen P e he (Formalism.L2.Host.unif P) (Formalism.L2.Host.unif_spec P) _
    (Formalism.L2.JoinChr.locU_val hee _) _ (D.nd.plOm.2 P) hine σ hσ
  change ((charOf ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)))
    (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) _ : Circle) : ℂ) = _
  rw [charOf, MonoidHom.comp_apply, MonoidHom.comp_apply, hpull, unitPart_of_pow hn]
  · simp
  · rw [← map_pow, ← map_inv, ← map_pow, map_pow (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)), hpow, map_one]

def frobU (D : D7) (P : PlE D.host) : G D.host.E D.nd.Om :=
  (GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)).choose

theorem frobU_spec (D : D7) (P : PlE D.host) : IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) (frobU D P) :=
  (GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)).choose_spec.2

def uD (D : D7) : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ := fun i b P =>
  Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) (frobU D P))

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}

theorem isDeltaInv_uD {D : D7} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (hρ : ρ.Good)
    (hpin : RealPin Rl cG ρ) : IsDeltaInv ρ (uD D) := by
  intro i j b k P hk α z hα hz
  obtain ⟨-, -, hsp, hP⟩ := hk
  have hdQ : Bridge.SplitOff P (((ρ.B i j b).de.Q : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.SplitOffS0.main hρ i _ (fun P' hP' => by
      rw [hρ.delta i j b] at hP'
      exact D.ntw.primes_subset_exceptional i (mem_half.1 hP').1) P hsp hP
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hdQ.1
  have hee : e * e = e := he.1.1
  have h1 := (hpin.delta i j b).2 P e (GlobalTheory.HeckeDetChar.isPlIdem he) (Formalism.L2.Host.unif P) _
    (Formalism.L2.JoinChr.locU_val hee (Formalism.L2.Host.unif P))
  have h2 := chi_locU_unif hρ i j b P hP (GlobalTheory.HeckeDetChar.isPlIdem he) hee (frobU D P) (frobU_spec D P)
  rw [GlobalTheory.HeckeDetChar.chi_detAt (hpin.delta i j b) (hρ.base i j b).de.unram (hρ.base i j b).de.split hdQ hα hz,
    show (((Rl.C.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) = (((ρ.B i j b).de.chi (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif P)) : Circle) : ℂ)
      from h1.symm, h2, inv_pow, inv_inv]
  rfl

end GlobalTheory.TwInputs.HeckePinRead

namespace GlobalTheory.TwInputs

end GlobalTheory.TwInputs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.LocKerMod

def idxAt {D : D7} (T : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : w.under (𝓞 D.host.F) = v) (g : GlobalTheory.FinZeta.Gv T v) : ℕ :=
  ((GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup.map
    (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom).relIndex
    (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup

end GlobalTheory.LocKerMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvPlaceNormProductMemCoefficientRingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_place_norm_product_mem_coefficient_ring : ∀ (D : D7) (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) (Q : Finset (Pl D.host.E)), Disjoint Q (D.ntw.S0 i) → ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eO i b).range := by
  first | exact @GlobalTheory.NormUnit.normProd_inv_mem | exact GlobalTheory.NormUnit.normProd_inv_mem | (intros; apply GlobalTheory.NormUnit.normProd_inv_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KSpan
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.MSpanDecay

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def kSpan : Submodule ℂ (GA E a → ℂ) :=
  Submodule.span ℂ {F | ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (G : GA E a → ℂ), GlobalTheory.JSW.IsRapidInf ν k γ ∧ Good G ∧
      F = fun g => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν}

end GlobalTheory.MSpanDecay
end
end

