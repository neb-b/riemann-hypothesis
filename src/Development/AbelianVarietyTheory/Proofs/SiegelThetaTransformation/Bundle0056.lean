module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionZeroAndNorm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0059
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaInnerEqConstMulTestInner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerVacIp

variable {D : D7} {S T : HSp D} (C : Ctx S T)

theorem isONFr_xB (B : C.Bas) (hB : C.IsB B) : IsONFr C.X (C.xB B) := by
  unfold IsONFr
  intro τ
  have h1 : ∀ x y : T.V, star (T.hT x y) = T.hT y x := by
    intro x y
    exact T.herm.eq x y
  have h2 : ∀ x : D.host.E, tauE D (C.m.e.symm τ) (star x) = (starRingEnd ℂ) (tauE D (C.m.e.symm τ) x) := by
    intro x
    unfold tauE
    dsimp only [star, Formalism.BasicNotions.Host.cmStar]
    exact IsCMField.complexEmbedding_complexConj D.host.E (D.host.emb ↑(D.eTau (C.m.e.symm τ))) x
  have key : ∀ i j, (τ : D.host.E →+* ℂ) (C.X.Gm i j) = tauE D (C.m.e.symm τ) (HSpace.gram T i j) := by
    intro i j
    have he := C.m.e_emb (C.m.e.symm τ)
    rw [Equiv.apply_symm_apply] at he
    rw [he, C.m.gT, Matrix.transpose_apply, NumberField.ComplexEmbedding.conjugate_coe_eq, ← h2]
    unfold HSpace.gram
    rw [h1]
  rw [← hB (C.m.e.symm τ)]
  ext a b
  unfold FD.gram mat Ctx.xB hermC FD.col gramAt
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Complex.star_def, Complex.conj_conj, Finset.sum_mul, key]
  rw [Finset.sum_comm]

theorem rho_zero_pt (f : WO S T → ℂ) : C.rho 0 f = f := by
  unfold Ctx.rho heisO
  funext w
  simp [symplOH, symplO, hO]

theorem zOf_zero (x : Frame C.X.Ψ T.rank) : C.zOf x 0 = 0 := by
  unfold Ctx.zOf Ctx.realPt zR
  funext k i
  simp [compAt, hermC]
  intro _
  simp only [← Pi.zero_def, Matrix.mulVec_zero, Pi.zero_apply]

theorem ip_vacua : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)),
    IsCovolOne (ratL T S) μ 𝓕 → ∃ a : ℂ, a ≠ 0 ∧ ∀ B, C.IsB B → ∀ φ φ' : TF S.rank C.g, SW.IsSB φ → SW.IsSB φ' →
      ipO μ 𝓕 (C.Th (C.xB B) φ) (C.Th (C.xB B) φ') = a * ip φ φ' := by
  intro D S T C μ 𝓕 hμ
  have h0 : IsRealPt (0 : WO S T) := by
    unfold IsRealPt
    simp
  have hg : ∀ x : Frame C.X.Ψ T.rank, gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := by
    intro x
    unfold gaussR
    simp [hx]
  obtain ⟨a, ha, b, -, hdbl⟩ :=
    GlobalTheory.SW.dbl_zero_and_norm D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even
  obtain ⟨⟨κ, hκ, hk⟩, -⟩ :=
    GlobalTheory.Ker.kZero_onFr_const_entire D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even
  refine ⟨a * κ, mul_ne_zero ha (Complex.ofReal_ne_zero.mpr hκ.ne'), ?_⟩
  intro B hB φ φ' hφ hφ'
  obtain ⟨hdom, hk0⟩ := hk _ (isONFr_xB C B hB)
  have h := _root_.GlobalTheory.Ker.GaussKer.ipO_rho_Th D S T C μ 𝓕 hμ _ hdom _ hdom φ φ' hφ hφ' 0 0 h0 h0
  rw [rho_zero_pt, rho_zero_pt, zOf_zero, hg] at h
  have hz : (fun k i => (starRingEnd ℂ) ((0 : Fin S.rank → Fin C.g → ℂ) k i)) = 0 := by
    funext k i
    simp
  rw [hz, hk0, (hdbl φ φ' hφ hφ').1] at h
  rw [h]
  simp only [map_one, one_mul]
  ring

end GlobalTheory.KerVacIp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicConnectionValueEqPolynomialDerivative
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem nab_harm_val_eq_polyDeriv : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (th : Fin n → (Fin g → ℂ) → ℂ), (∀ b, A.Reads ((N : ℤ) ^ 2) (F b) (th b)) → ∑ m ∈ P.support, algebraMap c.F ℂ (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) = I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (fun ℓ => (Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1) : Fin n → Fin g → ℂ)) (fun z => ∏ b, th b (z b)) 0 := by
  intro hC E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A h1 h2 h3 _ nab hn n N a P hP
  obtain ⟨Φ, -, -, -, -, -, hRd, -⟩ := _root_.GlobalTheory.Dict.AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A h1 h2 h3
  have hk : ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) := by push_cast; rfl
  rw [hk]
  intro F th hF
  have key := _root_.GlobalTheory.AnVal.harm_nab_eq_polyDeriv hC E H Dw l Xo c y g _ e Φ nab hn (N ^ 2) n F th
    (fun b => (hRd _ _ _).2 (hF b)) a P hP
  rw [key]
  congr 1

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatticeVacuaTensorCorrespondLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem epsW_neg_rows {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (X : Data E r) (w : E)
    (y : Matrix (Fin n) (Fin r) E) : SW.epsW X w (-y) = SW.epsW X w y := by
  have key : ∀ k, EF X ((-y) k) (w • (-y) k) = EF X (y k) (w • y k) := by
    intro k
    change (SW.EFBil X) (-(y k)) (w • -(y k)) = (SW.EFBil X) (y k) (w • y k)
    rw [smul_neg]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  unfold SW.epsW
  rw [Finset.sum_congr rfl (fun k _ => key k)]

theorem latVac_th_iff (D : D7) (S T : HSp D) (C : Ctx S T) (w : D.host.E) (hw : IsIntegral ℤ w)
    (h1 : w + cc w = 1) (h2 : IdemTwo w) (M : ℕ) (Λ : Lt D.host.E S.rank) (hΛ : Λ ∈ Vset D.host.E S.rank M)
    (L : Lt D.host.E T.rank) (hL : SelfD C.X L) (x : Frame C.X.Ψ T.rank) (hx : x ∈ C.X.dom)
    (φ : TF S.rank C.g) (hφ : SW.IsSB φ) :
    IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) (C.Th x φ) ↔
      ∀ y ∈ tens Λ L, SW.epsW C.X w y • heisG C.X C.bas y φ = φ := by
  have hth : C.IsTh (C.Th x φ) := (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C x hx φ hφ).1.1
  rw [GlobalTheory.T.isLatticeVacuum_iff_signedRational_fixed D S T C w hw h1 h2 M Λ hΛ L hL _ hth]
  have hsb : ∀ y, SW.IsSB (heisG C.X C.bas y φ) := fun y =>
    ((GlobalTheory.SW.heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 y φ hφ).1
  have hrho := (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ).2.2.1
  constructor
  · intro h y hy
    have h' := h (-y) (neg_mem hy)
    rw [hrho, neg_neg, epsW_neg_rows] at h'
    have hsb' : SW.IsSB (SW.epsW C.X w y • heisG C.X C.bas y φ) :=
      GlobalTheory.SW.TensVac.rho_sb (idx := C.idx) (hs := C.sympl) (hn := C.even) y hφ
    rw [← (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C x hx _ (hsb y)).2.1] at h'
    exact ((_root_.GlobalTheory.Ker.Ctx.th_laws D S T C x hx _ hsb').1 φ hφ).2 h'
  · intro h y hy
    have h' := h (-y) (neg_mem hy)
    rw [epsW_neg_rows] at h'
    rw [hrho, ← (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C x hx _ (hsb (-y))).2.1, h']

theorem latVac_th_line : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∀ (M : ℕ), ∀ Λ ∈ Vset D.host.E S.rank M, ∀ L : Lt D.host.E T.rank, SelfD C.X L → (∀ x ∈ C.X.dom, ∀ φ : TF S.rank C.g, SW.IsSB φ → (IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) (C.Th x φ) ↔ ∀ y ∈ tens Λ L, SW.epsW C.X w y • heisG C.X C.bas y φ = φ)) ∧ ∀ B, C.IsB B → ∀ v, IsVac C.X C.bas w (tens Λ L) v → ∀ f, C.IsTh f → C.IsFock B f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f → ∃ t : ℂ, f = t • (C.Th (C.xB B) v) := by
  intro D S T C w hw h1 h2 M Λ hΛ L hL
  refine ⟨fun x hx φ hφ => latVac_th_iff D S T C w hw h1 h2 M Λ hΛ L hL x hx φ hφ, ?_⟩
  intro B hB v hv f hf hF hlat
  obtain ⟨φ, hφ, rfl⟩ := _root_.GlobalTheory.Ker.exists_test_of_fock D S T C B hB f hf hF
  have hx : C.xB B ∈ C.X.dom := ((_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.1
  have hfix := (latVac_th_iff D S T C w hw h1 h2 M Λ hΛ L hL (C.xB B) hx φ hφ).1 hlat
  have hline := (GlobalTheory.SW.TensVac.vacua D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even
    w hw h1 L hL M Λ hΛ).2.1 v φ hv hφ hfix
  refine ⟨SW.ip φ v, ?_⟩
  calc C.Th (C.xB B) φ = C.Th (C.xB B) (SW.ip φ v • v) := by rw [← hline]
    _ = SW.ip φ v • C.Th (C.xB B) v := (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C _ hx v hv.1).2.1 _

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThBijFock
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem th_bij_fock : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → (∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsZak (C.xB B) φ (C.Th (C.xB B) φ) ∧ C.IsFock B (C.Th (C.xB B) φ)) ∧ (∀ f, C.IsTh f → C.IsFock B f → ∃! φ : TF S.rank C.g, SW.IsSB φ ∧ f = C.Th (C.xB B) φ) := by
  intro D S T C B hB
  have hx : C.xB B ∈ C.X.dom := ((_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.1
  refine ⟨fun φ hφ => ⟨(_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hx φ hφ).1, ((_root_.GlobalTheory.Ker.fvec_Th_zero D S T C).2 B hB φ hφ).1⟩, ?_⟩
  intro f hf hF
  obtain ⟨φ, hφ, rfl⟩ := _root_.GlobalTheory.Ker.exists_test_of_fock D S T C B hB f hf hF
  refine ⟨φ, ⟨hφ, rfl⟩, ?_⟩
  rintro ψ ⟨hψ, h⟩
  exact (((_root_.GlobalTheory.Ker.Ctx.th_laws D S T C _ hx φ hφ).1 ψ hψ).2 h).symm

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionTranslatesThetaByUnitScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.RealScalar

variable {D : D7} {S T : HSp D}

theorem mul_tmul_eq_zero {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E] [Algebra F A]
    [Algebra F B] [Algebra F E] {a : (A × B) ⊗[F] E}
    (ha : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) a = 0) (y : E) :
    a * (((0, 1) : A × B) ⊗ₜ[F] y) = 0 := by
  have key : ∀ a : (A × B) ⊗[F] E, a * (((0, 1) : A × B) ⊗ₜ[F] y) =
      TensorProduct.map (LinearMap.inr F A B) LinearMap.id
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) a * ((1 : B) ⊗ₜ[F] y)) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [add_mul, ha, hb, map_add (f := _), add_mul, map_add (f := _)]
    | tmul x e =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  rw [key, ha, zero_mul, map_zero]

theorem mul_mul_eq_self {R R' : Type} [CommRing R] [CommRing R'] (p : R →+* R') {m n : ℕ}
    {a : Matrix (Fin m) (Fin m) R} {b : Matrix (Fin n) (Fin n) R} {x : Matrix (Fin m) (Fin n) R}
    (ha : a.map p = 1) (hb : b.map p = 1) (hx : ∀ c, p c = 0 → ∀ i j, c * x i j = 0) : a * x * b = x := by
  have k : ∀ {l : ℕ} {c : Matrix (Fin l) (Fin l) R}, c.map p = 1 → ∀ i j, p ((c - 1) i j) = 0 := by
    intro l c hc i j
    have h2 : p (c i j) = (1 : Matrix (Fin l) (Fin l) R') i j := congrFun (congrFun hc i) j
    rw [Matrix.sub_apply, map_sub, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e1 : (a - 1) * x = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun l _ => hx _ (k ha i l) _ _
  have e2 : x * (b - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun l _ => by
      rw [mul_comm]
      exact hx _ (k hb l j) _ _
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at e1
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at e2
  rw [e1, e2]

theorem map_finPart_mt {V : HSp D} {g : GA D V} (hg : g ∈ GinfC V) : (mt V g).map (finPart D) = 1 := by
  have h1 : finHom V g = 1 := hg
  exact congrArg Units.val h1

theorem actO_finW {h : GA D S} (hh : h ∈ GinfC S) {g : GA D T} (hg : g ∈ GinfC T)
    (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : actO S T h g (finW S T y) = finW S T y :=
  mul_mul_eq_self (finPart D) (map_finPart_mt hg) (map_finPart_mt (inv_mem hh)) fun _ hc i j =>
    mul_tmul_eq_zero (F := D.host.F) (A := Ainf D.host.F) (B := Af D.host.F) hc (y j i)

theorem rho_zero (C : Ctx S T) (f : WO S T → ℂ) : C.rho 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem zOf_zero (C : Ctx S T) (x : Frame C.X.Ψ T.rank) : C.zOf x 0 = 0 := by
  have h0 : C.realPt 0 = 0 := by
    funext σ k a
    simp [Ctx.realPt, compAt]
  funext k i
  simp [Ctx.zOf, h0, zR, hermC]

theorem gaussR_zero (C : Ctx S T) (x : Frame C.X.Ψ T.rank) :
    gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := by
  simp [gaussR, hx]

theorem exists_ipO_Th (C : Ctx S T) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) : ∃ a : ℂ, a ≠ 0 ∧ ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, SW.IsSB φ →
      ipO μ 𝓕 (C.Th (C.xB B) φ) (C.Th (C.xB B) φ) = a * SW.ip φ φ := by
  obtain ⟨a, ha, b, hab⟩ := GlobalTheory.SW.dbl_zero_and_norm D.host.E T.rank C.X C.g C.bas C.idx S.rank
    C.sympl C.even
  obtain ⟨⟨κ, hκ, hk⟩, -⟩ := GlobalTheory.Ker.kZero_onFr_const_entire D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx
    S.rank C.sympl C.even
  refine ⟨a * κ, mul_ne_zero ha (by exact_mod_cast hκ.ne'), fun B hB φ hφ => ?_⟩
  obtain ⟨hon, hdom, -⟩ := (_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB
  have h0 : IsRealPt (0 : WO S T) := by
    ext i j
    simp
  have := _root_.GlobalTheory.Ker.GaussKer.ipO_rho_Th D S T C μ 𝓕 hμ _ hdom _ hdom φ φ hφ hφ 0 0 h0 h0
  have e : (fun (k : Fin S.rank) (i : Fin C.g) => conj ((0 : Fin S.rank → Fin C.g → ℂ) k i)) = 0 := by
    funext k i
    simp
  rw [rho_zero, zOf_zero, gaussR_zero, e, (hk _ hon).2, (hab.2 φ φ hφ hφ).1] at this
  rw [this]
  simp only [map_one]
  ring

theorem om_real_Th : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ h ∈ GinfC S, ∀ g ∈ GinfC T, ∀ B, C.IsB B → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ φ : TF S.rank C.g, SW.IsSB φ → om (h, g) (C.Th (C.xB B) φ) = c • (C.Th (C.xB (C.mvB g B)) φ) := by
  intro D S T C om hom h hh g hg B hB
  obtain ⟨-, hdom, -, -, -, hmv⟩ := (_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB
  have hB' : C.IsB (C.mvB g B) := (hmv g).1
  obtain ⟨-, hdom', -⟩ := (_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 _ hB'
  have hth : ∀ x ∈ C.X.dom, ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsTh (C.Th x φ) :=
    fun x hx φ hφ => (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C x hx φ hφ).1.1
  have hex : ∀ φ : TF S.rank C.g, ∃ φ' : TF S.rank C.g, SW.IsSB φ →
      SW.IsSB φ' ∧ om (h, g) (C.Th (C.xB B) φ) = C.Th (C.xB (C.mvB g B)) φ' := by
    intro φ
    by_cases hφ : SW.IsSB φ
    · obtain ⟨φ', h'⟩ := _root_.GlobalTheory.Ker.exists_test_of_fock D S T C _ hB' _ (hom.om_pres (h, g) _ (hth _ hdom φ hφ))
        (((_root_.GlobalTheory.Ker.WeakMove.om_move D S T C om hom h g _ (hth _ hdom φ hφ)).2 B hB).1
          ((_root_.GlobalTheory.Ker.fvec_Th_zero D S T C).2 B hB φ hφ).1)
      exact ⟨φ', fun _ => h'⟩
    · exact ⟨φ, fun h' => absurd h' hφ⟩
  choose A hA using hex
  have L := _root_.GlobalTheory.Ker.Ctx.th_laws D S T C
  have hadd : ∀ φ ψ : TF S.rank C.g, SW.IsSB φ → SW.IsSB ψ → SW.IsSB (φ + ψ) :=
    fun φ ψ h h' => (isSB_algebra_haar_linear _ _ _ _ _ h h').1
  have hsm : ∀ (a : ℂ) (φ : TF S.rank C.g), SW.IsSB φ → SW.IsSB (a • φ) :=
    fun a φ h => (isSB_algebra_haar_linear _ _ _ _ _ h h).2.1 _
  have hhe : ∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (φ : TF S.rank C.g), SW.IsSB φ →
      SW.IsSB (heisG C.X C.bas y φ) := fun y φ h =>
    ((GlobalTheory.SW.heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 y φ h).1
  obtain ⟨c, hc⟩ := GlobalTheory.Ker.schur_heisG D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even A
    (fun φ hφ => (hA φ hφ).1)
    (fun φ ψ hφ hψ => by
      have h1 := hA _ (hadd _ _ hφ hψ)
      refine ((L _ hdom' _ h1.1).1 _ (hadd _ _ (hA φ hφ).1 (hA ψ hψ).1)).2 ?_
      rw [← h1.2, ((L _ hdom _ hφ).1 _ hψ).1, map_add (f := _), (hA φ hφ).2, (hA ψ hψ).2,
        ((L _ hdom' _ (hA φ hφ).1).1 _ (hA ψ hψ).1).1])
    (fun a φ hφ => by
      have h1 := hA _ (hsm a _ hφ)
      refine ((L _ hdom' _ h1.1).1 _ (hsm a _ (hA φ hφ).1)).2 ?_
      rw [← h1.2, (L _ hdom _ hφ).2.1, map_smul, (hA φ hφ).2, (L _ hdom' _ (hA φ hφ).1).2.1])
    (fun y φ hφ => by
      have h1 := hA _ (hhe y _ hφ)
      refine ((L _ hdom' _ h1.1).1 _ (hhe y _ (hA φ hφ).1)).2 ?_
      have e1 := (L _ hdom _ hφ).2.2.1 (-y)
      have e2 := (L _ hdom' _ (hA φ hφ).1).2.2.1 (-y)
      rw [neg_neg] at e1 e2
      rw [← h1.2, ← e1, ← e2, ← (hA φ hφ).2, hom.om_heis h g _ _ (hth _ hdom φ hφ), actO_finW hh hg])
  have hc' : ∀ φ : TF S.rank C.g, SW.IsSB φ →
      om (h, g) (C.Th (C.xB B) φ) = c • (C.Th (C.xB (C.mvB g B)) φ) := fun φ hφ => by
    rw [(hA φ hφ).2, hc φ hφ, (L _ hdom' _ hφ).2.1]
  by_cases hne : ∃ φ : TF S.rank C.g, SW.IsSB φ ∧ φ ≠ 0
  · obtain ⟨φ, hφ, h0⟩ := hne
    refine ⟨c, ?_, hc'⟩
    obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := _root_.GlobalTheory.Ker.ScalarProduct.ip_basic D S T C
    obtain ⟨a, ha, hn⟩ := exists_ipO_Th C hμ
    have t1 := hth _ hdom φ hφ
    have t2 := hth _ hdom' φ hφ
    have t3 : C.IsTh (c • (C.Th (C.xB (C.mvB g B)) φ)) := hc' φ hφ ▸ hom.om_pres (h, g) _ t1
    have u := ((hip μ 𝓕 hμ _ t1).2.2.2 _ t1).2.2.2.2.2 om hom (h, g)
    rw [hc' φ hφ, ((hip μ 𝓕 hμ _ t2).2.2.2 _ t3).2.2.1, ((hip μ 𝓕 hμ _ t3).2.2.2 _ t2).2.1,
      ((hip μ 𝓕 hμ _ t2).2.2.2 _ t2).2.2.1, map_mul, ← ((hip μ 𝓕 hμ _ t2).2.2.2 _ t2).2.1,
      hn _ hB φ hφ, hn _ hB' φ hφ, ← mul_assoc, Complex.mul_conj'] at u
    have hz := mul_ne_zero ha (GlobalTheory.SW.DblZero.ip_self_ne_zero hφ h0)
    have u' : ((‖c‖ : ℂ)) ^ 2 = 1 := mul_right_cancel₀ hz (by rw [u, one_mul])
    have u'' : ‖c‖ ^ 2 = 1 := by exact_mod_cast u'
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 u''
  · refine ⟨1, norm_one, fun φ hφ => ?_⟩
    have h0 : φ = (0 : ℂ) • φ := by
      by_contra h0
      exact hne ⟨φ, hφ, fun e => h0 (by rw [e, smul_zero])⟩
    rw [h0, (L _ hdom _ hφ).2.1, (L _ hdom' _ hφ).2.1]
    simp

end GlobalTheory.Ker.RealScalar
end

