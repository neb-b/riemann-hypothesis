module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMatrixMajorantOperatorNormLeDefinite
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.DefiniteOpNorm

theorem span_colP {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (hp : X.p0 = r) (x : Frame X.Ψ r) (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) ℂ)
    (hA : (A * mat x τ).det ≠ 0) (w : Fin r → ℂ) :
    ∃ K : Fin X.p0 → ℂ, w = ∑ a, K a • Matrix.mulVec A (X.colP x τ a) := by
  classical
  set M := A * mat x τ with hM
  set c := M⁻¹.mulVec w with hc
  have hw : w = M.mulVec c := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
  refine ⟨fun a => c (Fin.castLE X.p0_le a), ?_⟩
  have hsum : ∀ f : Fin r → Fin r → ℂ,
      ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) = ∑ j : Fin r, f j := by
    intro f
    exact Fintype.sum_equiv (finCongr hp) _ _ (fun a => by congr 1)
  show w = ∑ a : Fin X.p0, (fun j => c j • A.mulVec (ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) j)) (Fin.castLE X.p0_le a)
  rw [hsum (fun j => c j • A.mulVec (ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) j))]
  conv_lhs => rw [hw]
  funext k
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, ReciprocityTheory.ChartRestriction.G.FD.col, hM, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem opNormLe_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 0 ∨ X.p0 = r) → ∀ x ∈ X.dom, ∀ β : GL (Fin r) E,
    (∀ v w, herm X.Gm (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v)
      (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) w) = herm X.Gm v w) →
    ∀ τ : X.Ψ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.OpNormLe X x τ (β : Matrix (Fin r) (Fin r) E)
      (Real.exp (1 / (3 * (r : ℝ)))) := by
  intro E _ _ _ r X hp x hx β hβ τ u
  set g : Matrix (Fin r) (Fin r) ℂ := (β : Matrix (Fin r) (Fin r) E).map τ.1 with hg
  set g' : Matrix (Fin r) (Fin r) ℂ := ((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 with hg'
  have hgg : g * g' = 1 := by
    rw [hg, hg', ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact Matrix.map_one τ.1 τ.1.map_zero τ.1.map_one
  have hg'g : g' * g = 1 := by
    rw [hg, hg', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one τ.1 τ.1.map_zero τ.1.map_one
  have hdetg : g.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hgg
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdetx : (mat x τ).det ≠ 0 := (hx τ).1
  have hiso : ∀ u v, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g v) = hermC τ.1 X.Gm u v :=
    GlobalTheory.MajInv.hermC_stab X hβ τ.1
  have H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, Matrix.mulVec g (X.colP x τ c) = ∑ a, K a • X.colP x τ a := by
    intro c
    rcases hp with hp | hp
    · exact absurd c.isLt (by omega)
    · obtain ⟨K, hK⟩ := span_colP X hp x τ 1 (by rw [Matrix.one_mul]; exact hdetx)
        (Matrix.mulVec g (X.colP x τ c))
      exact ⟨K, by simpa only [Matrix.one_mulVec] using hK⟩
  have H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP x τ a = ∑ c, L c • Matrix.mulVec g (X.colP x τ c) := by
    intro a
    rcases hp with hp | hp
    · exact absurd a.isLt (by omega)
    · exact span_colP X hp x τ g (by rw [Matrix.det_mul]; exact mul_ne_zero hdetg hdetx) _
  have key : X.maj x τ (Matrix.mulVec g u) = X.maj x τ u := by
    have h := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_transfer X hx hx τ g g'
      (fun w => by rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]) hiso H1 H2 (Matrix.mulVec g u)
    rwa [Matrix.mulVec_mulVec, hg'g, Matrix.one_mulVec] at h
  rw [key]
  have h0 := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ u
  have h1 : (1 : ℝ) ≤ Real.exp (1 / (3 * (r : ℝ))) ^ 2 :=
    one_le_pow₀ (Real.one_le_exp (by positivity))
  nlinarith

end GlobalTheory.DefiniteOpNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumSplitSupportedEqIntertwinerMulHalfDetCh
section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Formalism.MainNotions.StandardLattice Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.SplitProj

namespace GlobalTheory.SplitWeilDict

theorem lemB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (w : 𝓞 D.host.E) (lam : ℕ →* ℂ) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
    GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om → GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam →
    ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ f (hf : IsThetaFunO ψ S T f), om (g, h) f = c • (Om (g, h) ⟨f, hf⟩ : WO S T → ℂ) := by
  intro D ψ hψ S T χS χT om hW ΛS ΛT w lam Om hL hlam g hg h hh
  obtain ⟨o, ho⟩ := exists_extend (thetaSub ψ S T) Om
  have ho' : ∀ p f (hf : IsThetaFunO ψ S T f), o p f = (Om p ⟨f, hf⟩ : WO S T → ℂ) := fun p f hf => ho p ⟨f, hf⟩
  have hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (o p f) := fun p f hf => by
    rw [ho' p f hf]
    exact (Om p ⟨f, hf⟩).2
  have hheis : ∀ (g' : GA D S) (k' : GA D T), g' ∈ GfC S → k' ∈ GfC T → ∀ u f, IsThetaFunO ψ S T f →
      o (g', k') (heisO ψ S T u f) = heisO ψ S T (actO S T g' k' u) (o (g', k') f) := by
    intro g' k' hg' hk' u f hf
    obtain ⟨f', h1, h2⟩ := hL.Heisenberg₂ hψ hg' hk' u ⟨f, hf⟩
    rw [ho' _ f hf, ← h2, ← h1]
    exact ho _ f'
  obtain ⟨c, hc, H⟩ := GlobalTheory.ThetaSchur.schur D ψ hψ S T (om (g, h) * o (g⁻¹, h⁻¹))
    (fun f hf => hW.om_pres _ _ (hpres _ _ hf))
    (fun u f hf => by
      rw [Module.End.mul_apply, Module.End.mul_apply, hheis _ _ (inv_mem hg) (inv_mem hh) u f hf,
        hW.om_heis _ _ _ _ (hpres _ _ hf), GlobalTheory.FinWeilForm.actO_actO_inv])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hW.om_unit μ 𝓕 hμ h𝓕 _ _ (hpres _ _ hf), ho' _ f hf,
        hL.unit hlam μ 𝓕 hμ h𝓕 _ ⟨f, hf⟩])
  refine ⟨c, hc, fun f hf => ?_⟩
  have h1 := H _ (hpres (g, h) f hf)
  rw [Module.End.mul_apply, ← Module.End.mul_apply (o _), ← map_mul,
    show ((g⁻¹, h⁻¹) * (g, h) : GA D S × GA D T) = 1 from inv_mul_cancel (g, h), map_one,
    Module.End.one_apply] at h1
  rw [h1, ho' _ f hf]

theorem lemC : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (w : 𝓞 D.host.E) (lam : ℕ →* ℂ) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
    GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om →
    (∀ g ∈ GfC S, ∀ h ∈ GfC T, ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ f (hf : IsThetaFunO ψ S T f), om (g, h) f = c • (Om (g, h) ⟨f, hf⟩ : WO S T → ℂ)) →
    ∀ (ε : AE D) (hε : GlobalTheory.RatAut.IsHalfIdem D ε), ∃ ν : GA D S × GA D T →* Circle, Continuous ν ∧
      ∀ (p : GA D S × GA D T) f (hf : IsThetaFunO ψ S T f),
        om (GlobalTheory.SplitProj.proj hε S p.1, GlobalTheory.SplitProj.proj hε T p.2) f =
          (ν p : ℂ) • (Om (GlobalTheory.SplitProj.proj hε S p.1, GlobalTheory.SplitProj.proj hε T p.2) ⟨f, hf⟩ : WO S T → ℂ) := by
  intro D ψ hψ S T χS χT om hW ΛS ΛT hS hT w lam Om hL hB ε hε
  let P : GA D S × GA D T →* GA D S × GA D T := (proj hε S).prodMap (proj hε T)
  have hPc : Continuous P := (continuous_proj hε).prodMap (continuous_proj hε)
  have hs : ∀ p : GA D S × GA D T, ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ f (hf : IsThetaFunO ψ S T f), om (P p) f = c • (Om (P p) ⟨f, hf⟩ : WO S T → ℂ) :=
    fun p => hB _ (proj_mem_GfC hε p.1) _ (proj_mem_GfC hε p.2)
  choose c hc h using hs
  obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  have hne : ∀ p, (Om p ⟨f, hf⟩ : WO S T → ℂ) ≠ 0 := fun p h0 => f0 (by
    have h1 : Om p ⟨f, hf⟩ = 0 := Subtype.ext h0
    have h2 := congrArg (Om p⁻¹) h1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at h2
    exact congrArg Subtype.val h2)
  refine ⟨MonoidHom.mk' (fun p => ⟨c p, mem_sphere_zero_iff_norm.2 (hc p)⟩) fun p q => Circle.ext ?_, ?_,
    fun p f hf => h p f hf⟩
  · show c (p * q) = c p * c q
    refine smul_left_injective ℂ (hne (P (p * q))) ?_
    show c (p * q) • (Om (P (p * q)) ⟨f, hf⟩ : WO S T → ℂ) = (c p * c q) • (Om (P (p * q)) ⟨f, hf⟩ : WO S T → ℂ)
    rw [← h _ f hf, map_mul P, map_mul om, Module.End.mul_apply, h q f hf, map_smul, h p _ (Om (P q) ⟨f, hf⟩).2,
      smul_smul, map_mul Om, Module.End.mul_apply, mul_comm (c q)]
  · refine Continuous.subtype_mk (continuous_iff_continuousAt.2 fun q => ?_) _
    obtain ⟨u, hu⟩ := Function.ne_iff.1 (hne (P q))
    have a1 : Continuous fun p => om (P p) f u := (hW.om_cont f hf u).comp hPc
    have a2 : Continuous fun p => (Om (P p) ⟨f, hf⟩ : WO S T → ℂ) u := (hL.cont hS hT ⟨f, hf⟩ u).comp hPc
    refine ((a1.continuousAt).div a2.continuousAt hu).congr ?_
    filter_upwards [a2.continuousAt.eventually_ne hu] with p hp
    show om (P p) f u / (Om (P p) ⟨f, hf⟩ : WO S T → ℂ) u = c p
    rw [h p f hf, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hp]

theorem lemD : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (w : 𝓞 D.host.E) (lam : ℕ →* ℂ) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
    GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om →
    (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) →
    ∀ e, IsSplitIdem D e → ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h →
    ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ c : ℂ, ‖c‖ = 1 →
    (∀ f (hf : IsThetaFunO ψ S T f), om (g, h) f = c • (Om (g, h) ⟨f, hf⟩ : WO S T → ℂ)) →
    c = (splitFacO χS χT x y : ℂ) := by
  intro D ψ hψ S T χS χT om hW ΛS ΛT w lam Om hL hsq e he g h hg hh x y hx hy c hc H
  obtain ⟨r, hr, a⟩ := hW.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', b⟩ := hL.split hsq he hg hh
  obtain ⟨ℓ, hℓ, f₁, hf₁, h0⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ hψ S T e he
  have k := a ℓ hℓ f₁ hf₁
  rw [H f₁ hf₁, map_smul, b ℓ hℓ ⟨f₁, hf₁⟩, smul_eq_mul] at k
  have k1 : (c * (r' : ℂ)) * ℓ f₁ = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) * ℓ f₁ := by
    rw [mul_assoc]; exact k
  have k2 := mul_right_cancel₀ h0 k1
  have k3 := congrArg norm k2
  rw [norm_mul, norm_mul, hc, Circle.norm_coe, one_mul, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hr'.le] at k3
  rw [k3, mul_comm] at k2
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne') k2

theorem splitWeil_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
  (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
  IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ lam : ℕ →* ℂ, GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam →
  (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) →
  ∀ (w : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
  GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om → ∀ ε : AE D, GlobalTheory.RatAut.IsHalfIdem D ε →
  ∀ (g : GA D S) (h : GA D T), SuppAt ε S g → SuppAt ε T h → ∀ x y : (AE D)ˣ, IsDetAt ε S g x → IsDetAt ε T h y →
  ∀ f : GlobalTheory.FinWeilO.thetaSub ψ S T,
    om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • (Om (g, h) f : WO S T → ℂ) := by
  intro D ψ hψ S T χS χT om hW ΛS ΛT hS hT lam hlam hsq w Om hL ε hε g₀ h₀ hg₀ hh₀ x₀ y₀ hx₀ hy₀ f₀
  have hB := lemB D ψ hψ S T χS χT om hW ΛS ΛT w lam Om hL hlam
  obtain ⟨ν, hνc, hν⟩ := lemC D ψ hψ S T χS χT om hW ΛS ΛT hS hT w lam Om hL hB ε hε
  obtain ⟨c, c1, c2, c3, c4, c5⟩ := GlobalTheory.FinWeilForm.exists_half_character hε S χT _ hW.hecT hW.resT
  obtain ⟨d, d1, d2, d3, d4, d5⟩ := GlobalTheory.FinWeilForm.exists_half_character hε T χS _ hW.hecS hW.resS
  obtain ⟨f₁, f1, hf₁⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  have hone : ∀ p : GA D S × GA D T, proj hε S p.1 = 1 → proj hε T p.2 = 1 → ν p = 1 := fun p a b => by
    have e := hν p f₁ hf₁
    rw [a, b, show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one, map_one, Module.End.one_apply,
      Module.End.one_apply] at e
    exact Circle.ext (smul_left_injective ℂ f1 (e.symm.trans (one_smul ℂ f₁).symm))
  have hsp : ∀ e, IsSplitIdem D e → ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h →
      ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ν (g, h) = splitFacO χS χT x y :=
    fun e he g h hg hh x y hx hy => by
      have e1 : ∀ f (hf : IsThetaFunO ψ S T f), om (g, h) f = (ν (g, h) : ℂ) • (Om (g, h) ⟨f, hf⟩ : WO S T → ℂ) :=
        fun f hf => by
          have := hν (g, h) f hf
          dsimp only at this
          rwa [proj_of_split hε he hg, proj_of_split hε he hh] at this
      exact Circle.ext (lemD D ψ hψ S T χS χT om hW ΛS ΛT w lam Om hL hsq e he g h hg hh x y hx hy _
        (Circle.norm_coe _) e1)
  have s1 : ∀ (V : HSp D) (a : AE D) i j, a * (Formalism.L2.Theta.mt V 1 - 1) i j = (Formalism.L2.Theta.mt V 1 - 1) i j :=
    fun V a i j => by rw [GlobalTheory.IdemSupport.mt_one, sub_self, Matrix.zero_apply, mul_zero]
  have d1' : ∀ (V : HSp D) (e : AE D), IsDetAt e V 1 1 := fun V e => by
    show ((1 : (AE D)ˣ) : AE D) = e * (Formalism.L2.Theta.mt V 1).det + (1 - e)
    rw [GlobalTheory.IdemSupport.mt_one, Matrix.det_one, Units.val_one]
    ring
  let μ : GA D S × GA D T →* Circle := ν * (c.comp (MonoidHom.fst _ _)) * (d.comp (MonoidHom.snd _ _))⁻¹
  have hμ : ∀ p, μ p = ν p * c p.1 * (d p.2)⁻¹ := fun p => rfl
  have hμc : Continuous μ := by
    show Continuous fun p : GA D S × GA D T => ν p * c p.1 * (d p.2)⁻¹
    exact (hνc.mul (c1.comp continuous_fst)).mul (d1.comp continuous_snd).inv
  have hl := GlobalTheory.LocalGlobalChar.eq_one_of_local D S (μ.comp (MonoidHom.inl _ _)) (hμc.comp (Continuous.prodMk_left 1))
    (fun g hg => by
      show μ (g, 1) = 1
      rw [hμ, hone (g, 1) (proj_of_real hε hg) (map_one _), c2 g hg]
      simp)
    (fun e he g hg => by
      show μ (g, 1) = 1
      obtain ⟨x, hx⟩ := GlobalTheory.FinWeilForm.exists_isDetAt he S g
      rw [hμ, hsp e he g 1 hg (s1 T _) x 1 hx (d1' T e), c4 e he g hg x hx, splitFacO]
      simp)
    (fun v η hv g hg => by
      show μ (g, 1) = 1
      rw [hμ, hone (g, 1) (proj_of_nonSplit hε hv hg) (map_one _), c3 v η hv g hg]
      simp)
  have hr := GlobalTheory.LocalGlobalChar.eq_one_of_local D T (μ.comp (MonoidHom.inr _ _)) (hμc.comp (Continuous.prodMk_right 1))
    (fun h hh => by
      show μ (1, h) = 1
      rw [hμ, hone (1, h) (map_one _) (proj_of_real hε hh), d2 h hh]
      simp)
    (fun e he h hh => by
      show μ (1, h) = 1
      obtain ⟨y, hy⟩ := GlobalTheory.FinWeilForm.exists_isDetAt he T h
      rw [hμ, hsp e he 1 h (s1 S _) hh 1 y (d1' S e) hy, d4 e he h hh y hy, splitFacO]
      simp)
    (fun v η hv h hh => by
      show μ (1, h) = 1
      rw [hμ, hone (1, h) (map_one _) (proj_of_nonSplit hε hv hh), d3 v η hv h hh]
      simp)
  have hall : ∀ p, μ p = 1 := fun p => by
    have : p = (p.1, 1) * (1, p.2) := Prod.ext (mul_one _).symm (one_mul _).symm
    rw [this, map_mul, show μ (p.1, 1) = 1 from hl p.1, show μ (1, p.2) = 1 from hr p.2, mul_one]
  have hνp : ν (g₀, h₀) = splitFacO χS χT x₀ y₀ := by
    have h1 := hall (g₀, h₀)
    rw [hμ, mul_inv_eq_one] at h1
    rw [splitFacO, ← c5 g₀ x₀ hx₀, ← d5 h₀ y₀ hy₀, ← h1]
    show ν (g₀, h₀) = (c g₀)⁻¹ * (ν (g₀, h₀) * c g₀)
    rw [mul_comm, mul_inv_cancel_right]
  have e := hν (g₀, h₀) f₀.1 f₀.2
  dsimp only at e
  rw [proj_of_suppAt hε hg₀, proj_of_suppAt hε hh₀, hνp] at e
  exact e

end GlobalTheory.SplitWeilDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroup
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.WeilLocalityW'

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (hTr : IsTriple B G X om om') (v : Pl (F := F)) (h : UA σ G.W.J) (hh : h ∈ UAt σ G.W (evFin F v))
    (u : AF F) (hu : evFin F v u = 0) (p q : Fin a' × Fin (a + a') → AF F)
    (Φ : (Fin a' × Fin (a + a') → AF F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a'))) :
      om' (1, h) (GlobalTheory.WeilM.schr B.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr B.ψ (u • p, u • q) (om' (1, h) Φ) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  set w := G.M'.co.e.symm (p, q) with hw
  have he : G.M'.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (mat h - 1) = 0 := hh u hu
  have hact : GlobalTheory.WeilM.actAB (cA σ) ((1, h) : UA σ G.V'.J × UA σ G.W.J) (u • w) = u • w := by
    have h1 : (u • w) * (mat h)ᵀ - u • w = w * (u • (mat h - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h0, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [mat] using h1
  have h2 := hW.impl (1, h) (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h2
  exact h2

theorem liftV_one_mul {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem locality : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v h hh φ hφ
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  set T := om' (1, h) with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (1, h) Φ hΦ
  have hcomm := comm_off B G X om om' hTr v h hh
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v B.ψ T hTr.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace B.ψ hTr.base.std) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ (1, h) Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin a' × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h' := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans, schr_trans] at h'
    exact h'
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a' × Fin (a + a')) v
  refine ⟨fun t => (R 0)⁻¹ * T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul]
      ring
    have hpat : At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := tens (evFin F v) φ R with hΦ₀
    set Φ₁ := tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin a' × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (_root_.GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
    have hfz : ∀ z, At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [tens, hpdef]
    field_simp

end GlobalTheory.WeilLocalityW'
end
end

