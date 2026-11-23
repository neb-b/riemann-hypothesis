module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0013
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBaseChangeEigenBasis
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeClauses
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

namespace GlobalTheory

theorem framedPoint_bcGenR (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) : BcGenRSt Xo c := by
  intro p T _ _ ψ y
  obtain ⟨z, hx, -, pm, h1, h2, h3⟩ :=
    GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c p.R T ψ y
  obtain ⟨x, _, _, _, _, _, s, gen⟩ := z
  dsimp only at hx pm h1 h2 h3
  subst hx
  have hpm : pm = bcPm ψ.toRingHom y.x := by
    apply pullback.hom_ext
    · exact h2.trans (bcPm_fst _ _).symm
    · exact h1.trans (bcPm_snd _ _).symm
  subst hpm
  exact ⟨s, h3, gen⟩

theorem framedPoint_baseChange_clauses :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), BcLieAnySt Xo c ∧ BcLieRSt Xo c ∧ BcGenRSt Xo c ∧ FrBCFieldSt Xo c := by
  intro E _ _ _ H Dw l Xo c
  refine ⟨?_, ?_, framedPoint_bcGenR E H Dw l Xo c, ?_⟩
  · intro S _ _ K _ _ ψ y τ w hw he
    exact GlobalTheory.frame_baseChange_eigen_basis E H Dw l Xo c S K ψ y τ w hw he
  · intro p T _ _ ψ y τ w hw he
    exact GlobalTheory.frame_baseChange_eigen_basis E H Dw l Xo c p.R T ψ y τ w hw he
  · intro S _ _ y K _ _ ψ
    exact GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c S K ψ y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsThClsDGalRul
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

namespace GlobalTheory.GalTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem covAut_eF {n : ℕ} (d : DeltaDat Xo c n) (ta : c.F ≃+* c.F) (a : c.F) :
    covAut d ta (d.eF a) = d.eF (ta a) := by
  show d.eF (ta (d.eF.symm (d.eF a))) = _
  rw [AlgEquiv.symm_apply_apply]

theorem thLa_conj (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {n : ℕ} (d : DeltaDat Xo c n) (ta : c.F ≃+* c.F)
    (h₂ : Fixes d.c₂ (covAut d ta)) [StarRing (𝓞 E)] (hN : IsNab d.Xo₂ d.c₂ d.nab₂) (u : c.F) (hu : u ≠ 0)
    (w w' : (Fin n → LevQ Dw d.l₂) → c.F) (hw : ∀ q, ta (w q) = u * w' q) (La : GenLat E n) (N : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (k : Type) [CommRing k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k) (v : Tw (covAut d ta) k)
    (hv : thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) La N
      (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) (twPt h₂ y₂) v) :
    thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w' q)) La N
      (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (MvPolynomial.map (ta : c.F →+* c.F) P)) y₂
      (algebraMap d.c₂.F k (d.eF u⁻¹) * v.val) := by
  have h1 := _root_.GlobalTheory.GalTw.shortValAt_conj hC E H Dw d.l₂ d.Xo₂ d.c₂ (covAut d ta) h₂ d.nab₂ hN n a _
    ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a P hP) _ La 1 N k y₂ v hv
  have h3 := (_root_.GlobalTheory.GalTw.phiHat_aut_and_mul E H Dw d.l₂ d.Xo₂ d.c₂ n).2.2 d.nab₂ _ La _ (d.eF u⁻¹) N _ k y₂ _ h1
  have e1 : (fun q => d.eF u⁻¹ * covAut d ta (d.eF (w q))) = fun q => d.eF (w' q) := by
    funext q
    rw [covAut_eF, hw, ← map_mul, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  have e2 : MvPolynomial.map (covAut d ta : d.c₂.F →+* d.c₂.F) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) =
      MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (MvPolynomial.map (ta : c.F →+* c.F) P) := by
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    exact congrArg (fun g => MvPolynomial.map g P) (RingHom.ext fun a => covAut_eF d ta a)
  rw [e1, e2, map_one] at h3
  exact h3

theorem isThClsD_galRul : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ (n : ℕ) (d : DeltaDat Xo c n) (h₂ : Fixes d.c₂ (covAut d ta)), (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → ∀ (cx : Rul d.Xo₂ d.c₂) (ka u : c.F), ka ≠ 0 → u ≠ 0 → (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ (galRul h₂ d.cδ) y₂ = algebraMap d.c₂.F k (d.eF ka) * evR d.Xo₂ d.c₂ cx y₂) → ∀ (Cl : Type) [Fintype Cl] (w w' : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (a : (E →+* ℂ) × ℕ → ℕ), (∀ v, io v ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → (∀ k q, ta (w k q) = u * w' k q) → ∀ x x' : Cl → Vs, (∀ k, io (x' k) = MvPolynomial.map (ta : c.F →+* c.F) (io (x k))) → ∀ (m : ℕ), ∀ f ∈ sec Xo c a m, IsThClsD Xo c d w La Nc gam vol ep io x f → (ka * u)⁻¹ • galRul h f ∈ sec Xo c a m ∧ IsThClsD Xo c { d with cδ := cx } w' La Nc gam (ta vol) (fun k => ta (ep k)) io x' ((ka * u)⁻¹ • galRul h f) := by
  intro hC E _ _ _ H Dw l Xo c ta h n d h₂ hN hδ cx ka u hka hu hcx Cl _ w w' La Nc gam vol ep Vs _ _ io a hio hw
    x x' hx m f hf hT
  obtain ⟨_, hN⟩ := hN
  obtain ⟨hs, hv⟩ := (_root_.GlobalTheory.GalTw.galRul_sec_val_semilinear E H Dw l Xo c ta h).1 a m f hf
  have hv₂ := ((_root_.GlobalTheory.GalTw.galRul_sec_val_semilinear E H Dw d.l₂ d.Xo₂ d.c₂ (covAut d ta) h₂).1 0 0 d.cδ hδ).2
  refine ⟨Submodule.smul_mem _ _ hs, ?_⟩
  intro k _ _ A A₂ hk y y₂ hy
  letI A₂' : Algebra d.c₂.F k := A₂
  have hk' : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := hk
  obtain ⟨vc, hvc, he⟩ := @hT k _ _ (inferInstance : Algebra c.F (Tw ta k))
    (inferInstance : Algebra d.c₂.F (Tw (covAut d ta) k))
    (fun a => by
      show algebraMap d.c₂.F k (covAut d ta (d.eF a)) = algebraMap c.F k (ta a)
      rw [covAut_eF, hk'])
    (twPt h y) (twPt h₂ y₂) hy
  refine ⟨fun cl => algebraMap d.c₂.F k (d.eF u⁻¹) * vc cl, fun cl => ?_, ?_⟩
  · rw [hx]
    exact thLa_conj hC d ta h₂ hN u hu (w cl) (w' cl) (hw cl) (La cl) (Nc cl) a _ (hio _) k y₂ (vc cl) (hvc cl)
  · have e0 : evR Xo c ((ka * u)⁻¹ • galRul h f) y = algebraMap c.F k (ka * u)⁻¹ * evR Xo c (galRul h f) y :=
      evalAt_smul _ _ _ _ y
    have he' : evR Xo c (galRul h f) y = evR d.Xo₂ d.c₂ (galRul h₂ d.cδ) y₂ *
        ∑ cl, algebraMap c.F k (ta (vol * ((gam cl : c.F))⁻¹ * ep cl)) * vc cl := by
      rw [hv k y, hv₂ k y₂]
      exact he
    show _ = evR d.Xo₂ d.c₂ cx y₂ * _
    rw [e0, he', hcx k y₂, hk', hk']
    have hka' : algebraMap c.F k ka ≠ 0 := (map_ne_zero _).2 hka
    simp only [map_mul, map_inv₀, map_natCast, mul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun cl _ => ?_
    field_simp

end GlobalTheory.GalTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelCoverLargerCoeffFieldLyingOver
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.FieldBC

theorem frOver_isLev_ddBC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (n : ℕ) (d : DeltaDat Xo c n), (∀ (k : Type) [CommRing k] [Algebra c.F k] [Algebra c'.F k] [Algebra d.c₂.F k] [A₂ : Algebra (covCoeff hle d).F k] (h : AlgOver c c' hle k) (h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k) (y₂ : FrPt d.Xo₂ (covCoeff hle d) k) (y : FrPt Xo c' k), @FrOver E _ _ _ H Dw l Xo c' n (ddBC hle d) k _ _ A₂ y₂ y ↔ FrOver d (y₂.res (le_covCoeff hle d) h₂) (y.res hle h)) ∧ (d.IsLev → (ddBC hle d).IsLev) := by
  intro E _ _ _ H Dw l Xo c c' hle n d
  refine ⟨fun k _ _ _ _ _ _ _ _ _ => Iff.rfl, ?_⟩
  rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hB := (_root_.GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw d.l₂ d.Xo₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d)).1 0 0 d.cδ h8
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, hB.1, ?_⟩
  · intro k _ _ A A₂ hA y
    letI A₂' : Algebra (covCoeff hle d).F k := A₂
    letI B : Algebra c.F k := @resAlg E _ _ _ H l c c' hle k _ A
    letI B₂ : Algebra d.c₂.F k := @resAlg E _ _ _ H d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) k _ A₂'
    have h : @AlgOver E _ _ _ H l c c' hle k _ B A := fun _ => rfl
    have h₂ : @AlgOver E _ _ _ H d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) k _ B₂ A₂' := fun _ => rfl
    obtain ⟨z, hz⟩ := @h7 k _ _ B B₂ (fun a => hA (incF c c' hle a)) (@FrPt.res E _ _ _ H Dw l c c' hle Xo k _ B A h y)
    exact ⟨@FrPt.ext E _ _ _ H Dw d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) d.Xo₂ k _ B₂ A₂' h₂ z, hz⟩
  · intro k _ _ A₂ y₂
    letI A₂' : Algebra (covCoeff hle d).F k := A₂
    letI B₂ : Algebra d.c₂.F k := @resAlg E _ _ _ H d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) k _ A₂'
    have h₂ : @AlgOver E _ _ _ H d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) k _ B₂ A₂' := fun _ => rfl
    intro h0
    exact @h9 k _ _ B₂ _ ((@hB.2 k _ B₂ A₂' h₂ y₂).symm.trans h0)

end GlobalTheory.FieldBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleValueTestRingEqThetaValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem thValAt_evR_of_fromTest : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab x P f → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y → ThValAt Xo c nab y x P (evR Xo c f y) := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab a n x P hP f hf S _ _ y hy
  obtain ⟨w, hw, -⟩ := thValTot_of_chartIndep firstFiveLaws.1 hC E H Dw l Xo c nab hnab S y a n x P hP
  have key := thetaValue_natural firstFiveLaws.1 hC E H Dw l Xo c nab hnab _ S hy.choose_spec.choose
    hy.choose_spec.choose_spec.choose y hy.choose_spec.choose_spec.choose_spec a n x P hP _ w (hf _ _) hw
  have e : evR Xo c f y = w := by
    unfold evR Formalism.L2.Pj.evalAt
    rw [dite_eq_left hy]
    exact key
  rw [e]
  exact hw

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueAnalyticFrameEqPolyDerivFock
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem AnFr.e_natCast_smul_eq_pow {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) (z : Fin g → ℂ) (n : ℕ) : Φ.e ((n : ℂ) • z) = Φ.e z ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_smul, pow_zero]
    exact (Φ.e_ker 0).2 Φ.lat.zero_mem
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, Φ.e_add, ih, pow_succ]

theorem thValAt_eq_polyDeriv_fock : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ mk : Dw.La →+ (Fin g → ℂ), (∀ a, mk a ∈ Φ.lat) → (∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • mk a)) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ θ, Φ.toAnFr.Rd 1 y.s θ → ∀ (n : ℕ) (x x2 : Fin n → Dw.La), (∀ b, x2 b ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ b, x2 b - x b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v : ℂ, ThValAt Xo c nab y x P v → v = ((l.M : ℂ)⁻¹) ^ P.totalDegree * I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (letDir el) (fun z => ∏ b, fock Φ.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • mk (x2 b)) (fun w => θ ((l.M : ℂ) • w)) (z b)) 0 := by
  intro hC E _ _ _ H Dw l Xo c _ _ y g ty el Φ mk hlat hlin hlev nab hnab θ hθ n x x2 hx2 hx a P hP v hv
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hM : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 l.odd.pos.ne'
  have hV := fun b => _root_.GlobalTheory.AnVal.rd_vt_levPt E H Dw l Xo c y g ty el Φ mk hlat hlin hlev θ hθ (x b) (x2 b) (hx2 b) (hx b)
  have hpow : ∀ b, Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk (x2 b)) ^ (l.M ^ 2) = 1 := by
    intro b
    rw [← Φ.toAnFr.e_natCast_smul_eq_pow, smul_smul, Nat.cast_pow, mul_inv_cancel₀ (pow_ne_zero 2 hM), one_smul]
    exact (Φ.e_ker _).2 (hlat _)
  have hex := fun b => (GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo l.M l.odd (ptO Xo y.x) y.s).1
    (KilledBy Xo (l.Mb ^ 2)) (levPt Xo y.x (x b)) _ (hV b).1.2 (hpow b) (hV b).1.1
  choose F hF using hex
  have hw : ThValAt Xo c nab y x P (thExpr Xo c nab y P F) :=
    ⟨ℂ, inferInstance, inferInstance, AlgHom.id c.F ℂ, y, F,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id, GlobalTheory.FramedBaseChange.refl y, hF, rfl⟩
  have hvw : v = thExpr Xo c nab y P F :=
    GlobalTheory.thetaValue_natural hL hC E H Dw l Xo c nab hnab ℂ ℂ (AlgHom.id c.F ℂ) y y
      (GlobalTheory.FramedBaseChange.refl y) a n x P hP v _ hv hw
  have hN := _root_.GlobalTheory.AnVal.harm_nab_eq_polyDeriv hC E H Dw l Xo c y g ty el Φ nab hnab (l.M ^ 2) n F _
    (fun b => (hV b).2 (F b) (hF b)) a P hP.1
  rw [hvw, thExpr, map_inv₀, map_pow, map_natCast, ← inv_pow]
  exact congrArg _ hN

end GlobalTheory.AnVal
end

