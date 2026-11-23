module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelIntegrableOnUnitaryQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.FunObj

theorem routeBig_kerBig_integrableOn : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ g : GA D (G.V (.grid i (j + 1))), IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1))) := by
  intro D T L sc G hWC μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ g₁ g
  have hHF : GlobalTheory.SquareComm.IsHaarFD _ (M.ν (.grid (i + 1) (j + 1))) (M.fd (.grid (i + 1) (j + 1))) :=
    (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨p, hsig, hrk⟩ := _root_.GlobalTheory.FunObj.squareTriple_sig_rank_lt W t i j hT M hM
  have key : ∀ d ∈ Θ.support, Integrable (fun u => Θ d * (W.kerA (.right i (j + 1)) d.1.2 g u *
      W.kerA (.down t (i + 1) j) d.2 u g₁)) ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1)))) := by
    intro d hd
    obtain ⟨ε, X, χ, χ', ω, hω, hX, Φ, hΦ, h, c, he⟩ := _root_.GlobalTheory.FunObj.routeBig_kernel_product_eq_theta hL W B ρ t i j hT M hM Θ Θ' hΘ d hd g g₁
    obtain ⟨N, C, hmi⟩ := hWC D W.ψ W.θ W.θ_is ε _ X χ χ' ω hω p hsig (hX ▸ hrk) _ _ hHF Φ hΦ
    refine Integrable.const_mul ?_ _
    simp_rw [he]
    exact ((hmi h).1).const_mul c
  have e : kerBig W Θ g g₁ = fun u => ∑ d ∈ Θ.support, Θ d * (W.kerA (.right i (j + 1)) d.1.2 g u *
      W.kerA (.down t (i + 1) j) d.2 u g₁) := by
    funext u; rfl
  rw [IntegrableOn, e]
  exact integrable_finsetSum _ key

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteSeesawArrowKernelsProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigSeesaw

open GlobalTheory.RouteSeesaw

theorem swap_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (hT' : T'.gramᵀ = -(S.gram.submatrix e₁ e₁))
    (hS' : S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂)) {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT ω)
    {ω₀ : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ)} (hω₀ : IsWeilDatumO ψ S' T' χT χS ω₀)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (g : GA D S) (h : GA D T) (g' : GA D S') (h' : GA D T')
    (hh : Formalism.L2.Theta.mt T' h' = ((Formalism.L2.Theta.mt S g).map (cA D)).submatrix e₁ e₁)
    (hg : Formalism.L2.Theta.mt S' g' = ((Formalism.L2.Theta.mt T h⁻¹).submatrix e₂ e₂)ᵀ) :
    ω₀ (g', h') (fun u => f (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) :
      Matrix (Fin T.rank) (Fin S.rank) (AE D))) 0 = ω (g, h) f 0 := by
  obtain ⟨φ', c1, q1, m1, s1, d1⟩ := GlobalTheory.GrpConj.exists_conj_equiv D S T' e₁ hT'
  obtain ⟨φ, c2, q2, m2, s2, d2⟩ := GlobalTheory.InvTransposeIso.grp_contra D T S' e₂ hS'
  obtain ⟨L, hL, hLs, cL, cL', rL, iL, fL⟩ := GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec D S T S' T' e₁ e₂
  have m1' : ∀ h, Formalism.L2.Theta.mt T' h = ((Formalism.L2.Theta.mt S (φ' h)).map (cA D)).submatrix e₁ e₁ := fun h => by
    ext i j
    have t3 := congrArg (cA D) (congrFun (congrFun (m1 h) i) j)
    simp only [Matrix.map_apply, Formalism.L2.Theta.cA_cA] at t3
    exact t3.symm
  have hact : ∀ g h x, L (actO S' T' g h x) = actO S T (φ' h) (φ g) (L x) := by
    intro g h x
    have u1 : ((Formalism.L2.Theta.mt S (φ' h)).map (cA D))ᵀ * S.gram.map (incA D) =
        S.gram.map (incA D) * Formalism.L2.Theta.mt S (φ' h)⁻¹ := by
      have k := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram S (φ' h)
      have k2 : Formalism.L2.Theta.mt S (φ' h) * Formalism.L2.Theta.mt S (φ' h)⁻¹ = 1 := by
        simp only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]
      have k3 := congrArg (· * Formalism.L2.Theta.mt S (φ' h)⁻¹) k
      simp only [Matrix.mul_assoc, k2, Matrix.mul_one] at k3
      exact k3
    have u2 : Formalism.L2.Theta.mt T (φ g) = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ.submatrix e₂.symm e₂.symm := by
      rw [← m2]; simp
    have u3 : (Formalism.L2.Theta.mt T' h)ᵀ.submatrix e₁.symm e₁.symm = ((Formalism.L2.Theta.mt S (φ' h)).map (cA D))ᵀ := by
      rw [m1']; simp
    rw [hL]
    unfold actO
    rw [hL, u2, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.submatrix_mul_equiv _ _ _ e₂.symm,
      ← Matrix.submatrix_mul_equiv _ _ _ e₁.symm, u3]
    simp only [Matrix.mul_assoc, u1]
  have hs : ∀ x y, symplO S T (L x) (L y) = symplO S' T' x y := fun x y => by
    rw [hL, hL]; exact GlobalTheory.DarbouxSymp.symplO_darboux D S T S' T' e₁ e₂ hT' hS' x y
  obtain ⟨ω', hw, hω'⟩ := GlobalTheory.SwapWeil.isWeilDatumO_swap D ψ S T S' T' (by simpa using Fintype.card_congr e₂)
    (by simpa using Fintype.card_congr e₁) L φ.toMonoidHom
    φ'.toMonoidHom cL cL' rL hs iL fL c2 c1 q2 q1 hact s2 s1 d2 d1 χS χT ω hω
  have th : IsThetaFunO ψ S' T' (fun w => f (L w)) :=
    GlobalTheory.SwapWeil.theta_pull L cL (fun x hx => (rL x).2 hx) hs (fun x hx => (iL x).2 hx) (fun x hx => (fL x).2 hx) hf
  have a1 : φ' h' = g := by
    have k : h' = φ'.symm g := GlobalTheory.MixModel.mt_injective T' (by rw [hh, m1', MulEquiv.apply_symm_apply])
    rw [k, MulEquiv.apply_symm_apply]
  have a2 : φ g' = h := by
    have k : g' = φ.symm h := GlobalTheory.MixModel.mt_injective S' (by
      have := m2 (φ.symm h)⁻¹
      rw [inv_inv, map_inv, MulEquiv.apply_symm_apply] at this
      rw [hg, this, Matrix.transpose_transpose])
    rw [k, MulEquiv.apply_symm_apply]
  have k9 := congrFun (hω' g' h' f) 0
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, a1, a2, map_zero] at k9
  simp only [← hL]
  rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ hω.std S' T' χT χS ω₀ ω' hω₀ hw (g', h') _ th]
  exact k9

theorem adjM_mul_neg {D : D7} (S B : HSp D) (y : Matrix (Fin S.rank) (Fin B.rank) (AE D)) :
    adjM S B (HMul.hMul yᵀ ((negSp S).gram.map (incA D)) : Matrix (Fin B.rank) (Fin S.rank) (AE D)) =
      -GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG B (y.map (cA D)) := by
  have h2 := GlobalTheory.RouteCoords.inv_mul_gram S
  have h3 : (((negSp S).gram.map (incA D)).map (cA D))ᵀ = -(S.gram.map (incA D)) := by
    rw [GlobalTheory.RouteCoords.gram_conj_transpose, negSp_gram, Matrix.map_neg _ (map_neg _)]
  unfold adjM
  rw [Matrix.map_mul, transpose_mul, h3, transpose_map, transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_neg, h2,
    Matrix.neg_mul, Matrix.one_mul, Matrix.neg_mul]
  rfl


set_option maxHeartbeats 1000000 in
theorem seesaw_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T)
    (i j : Fin D.R.m) (M : Vol G) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : IsTripleOf W M t i j e Bs Γ X) (hTr : IsTriple Bs Γ X om om')
    (hT₁ : (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ).IsSymm) (hT₂ : (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ).Nondegenerate)
    (LT : Submodule (𝓞 D.host.E) (Fin (spW G i j).rank → D.host.E)) (hLT : LT.IsLattice D.host.E)
    (hUT : Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ) LT) (sgT : (D.host.E →+* ℂ) → ℕ × ℕ)
    (hS₁ : (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)).IsSymm)
    (hS₂ : (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)).Nondegenerate)
    (LS : Submodule (𝓞 D.host.E) (Fin ((spW G i j).rank + (spW₁ G i j).rank) → D.host.E)) (hLS : LS.IsLattice D.host.E)
    (hUS : Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)) LS) (sgS : (D.host.E →+* ℂ) → ℕ × ℕ)
    (ω : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) × GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) →*
      Module.End ℂ (WO (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) → ℂ))
    (hω : IsWeilDatumO W.ψ (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS)
      (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) (X.β / X.α) X.β ω)
    (g : GA D (spV G i j)) (g₁ : GA D (spV₁ G i j)), ∃ ξ : ℂ, ξ ≠ 0 ∧ ∀ (f₁ : WO (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) → ℂ)
      (f₂ : WO (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) → ℂ),
      IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) f₁ →
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) f₂ →
      ∀ (u : GA D (spW G i j)) (g' : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS))
        (h' : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT)),
      Formalism.L2.Theta.mt _ h' = (conjU (spW G i j) 1 h.JW u).1.1 → Formalism.L2.Theta.mt _ g' = ((blkU (spV G i j) (spV₁ G i j) e h.JWW (g, g₁))⁻¹).1.1ᵀ →
      W.kerA (.right i (j + 1)) f₁ g u * W.kerA (.down t (i + 1) j) f₂ u g₁ =
        ξ * ω (g', h') (fun x => f₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e x)ᵀ) *
          f₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e x)) 0 := by
  intro D T L sc G W t i j M e Bs Γ X om om' h hTr hT₁ hT₂ LT hLT hUT sgT hS₁ hS₂ LS hLS hUS sgS ω hω g g₁
  have hi := i.2
  have hj := j.2
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, hω₂, hadj⟩ := GlobalTheory.SquareDict.ExactBig.adjoint_exact h2
  have hcard : (spV G i j).rank + (spV₁ G i j).rank = (spW G i j).rank + (spW₁ G i j).rank := by
    simpa using Fintype.card_congr e
  have pV : (G.V (.grid i (j + 1))).rank % 2 = (G.V (.grid (i + 1) j)).rank % 2 := by
    have hev := hTr.geo.even
    rw [← hcard, Nat.even_iff] at hev
    simp only [spV, spV₁] at hev
    omega
  have cT : X.β / X.α = G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹ := by
    rw [h.α, h.β]
    simp only [GridData.chrT, GridData.chrS, GridData.chr, GlobalTheory.SquareDict.ExactBig.attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha]
    rw [pV, mul_div_mul_right_eq_div, ← div_eq_mul_inv, div_div_div_cancel_right]
  obtain ⟨ωA, hA⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D W.ψ W.ψ_std (negSp (spW G i j))
    (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) X.β (G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹)
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecT (hecke_mul' h1.hecT hω₂.hecT) hω.resT
    (resEta_mul h1.resT hω₂.resT)
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D _ g
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D _ g₁
  refine ⟨(((G.chrS (.chi i (j + 1)) / X.β) x : Circle) : ℂ) * ((((G.chrT (.mu t (i + 1) j))⁻¹ / X.β) y : Circle) : ℂ),
    mul_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _), fun f₁ f₂ hf₁ hf₂ u g' h' hh hg => ?_⟩
  have k := GlobalTheory.SquareDict.ExactBig.seesaw_exact h1 hω₂ hA hf₁ (hadj _ hf₂).1 (negGA _ u) g g₁ hx hy
  rw [(hadj _ hf₂).2] at k
  refine k.trans ?_
  congr 1
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let e₂ : Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ Fin ((spV G i j).rank + (spV₁ G i j).rank) :=
    e.symm.trans finSumFinEquiv
  have hb : ∀ {R : Type} [CommRing R] (A : Matrix (Fin (spV G i j).rank) (Fin (spV G i j).rank) R)
      (B : Matrix (Fin (spV₁ G i j).rank) (Fin (spV₁ G i j).rank) R),
      (GlobalTheory.Doubling.blkMat finSumFinEquiv A B).submatrix e₂ e₂ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A B := fun A B => by
    ext a b
    simp [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, e₂]
  have hJ : Γ.W.J = D.host.xi0 • ((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂ := by
    refine h.JWW.trans (congrArg (D.host.xi0 • ·) ?_)
    rw [GlobalTheory.Doubling.gram_hsum, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← hb]
    rfl
  have hJu : IsUnit Γ.W.J.det := by
    rw [hJ, det_smul, det_submatrix_equiv_self, det_transpose]
    exact (IsUnit.mk0 _ (pow_ne_zero _ hξ)).mul (GlobalTheory.MixModel.gram_isUnit_det _)
  have e0 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJu,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
  have hT' : (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT).gramᵀ =
      -((negSp (spW G i j)).gram.submatrix (Equiv.refl _) (Equiv.refl _)) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf, negSp_gram]
    show Γ.V.J = - -(spW G i j).gram
    rw [h.JW, one_smul, neg_neg]
  have hS' : (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS).gram⁻¹ =
      -(((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    refine e0.trans ?_
    rw [hJ, smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hξ, neg_one_smul]
  have hbox : IsThetaFunO W.ψ (negSp (spW G i j)) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j))
      (box2 (S := negSp (spW G i j)) (A := spV G i j) (B := spV₁ G i j) f₁
        (fun y => f₂ (adjM (spW G i j) (spV₁ G i j) y))) := by
    rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
    exact (GlobalTheory.BiTransfer.sumDec _ _).isThetaFunO_boxT hf₁ (hadj _ hf₂).1
  have hω' := hω
  rw [cT] at hω'
  have key := swap_eq (negSp (spW G i j)) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j))
    (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT)
    (Equiv.refl (Fin (spW G i j).rank)) e₂ hT' hS' hA hω'
    hbox (negGA _ u) (GlobalTheory.SquareComm.blk _ _ (g, g₁)) g' h' hh (by
      rw [hg, ← map_inv, Prod.inv_mk, GlobalTheory.SquareComm.mt_blk]
      exact congrArg transpose (hb (Formalism.L2.Theta.mt _ g⁻¹) (Formalism.L2.Theta.mt _ g₁⁻¹)).symm)
  refine key.symm.trans (congrArg (fun F => ω (g', h') F 0) ?_)
  funext z
  have k1 : ∀ a, e₂.symm (Fin.castAdd _ a) = e (.inl a) := fun a =>
    congrArg e (finSumFinEquiv_symm_apply_castAdd a)
  have k2 : ∀ a, e₂.symm (Fin.natAdd _ a) = e (.inr a) := fun a =>
    congrArg e (finSumFinEquiv_symm_apply_natAdd a)
  refine congrArg₂ (· * ·) (congrArg f₁ ?_) (congrArg f₂ ?_)
  · ext a b
    exact Finset.sum_congr (s₁ := Finset.univ) rfl fun c _ =>
      congrArg (fun s => z c s * incA D ((negSp (spW G i j)).gram c b)) (k1 a)
  · refine Eq.trans (congrArg (adjM (spW G i j) (spV₁ G i j)) ?_)
      (adjM_mul_neg (spW G i j) (spV₁ G i j) (z.submatrix id fun k => e (.inr k)))
    ext a b
    exact Finset.sum_congr (s₁ := Finset.univ) rfl fun c _ =>
      congrArg (fun s => z c s * incA D ((negSp (spW G i j)).gram c b)) (k2 a)

end GlobalTheory.BigSeesaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRanksSumLeTwoExponentAddCentre
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.ChiGrid

theorem botBig_add_botSmall_le_two_e_add_two_cen (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) :
    ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) ≤
      2 * ((GlobalTheory.ChiGrid.num D C τ).e (j + 1) + GlobalTheory.ChiGrid.cen D C τ (D.R.m - i)) := by
  set P := D.hc τ with hP
  set G := GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) 0 with hG
  obtain ⟨hv, hb, -⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) 0
  have he := (GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) (cen D C τ)).2.2 j
  have hne : (num D C τ).e (j + 1) = (GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) (cen D C τ)).e (j.1 + 1) := rfl
  have hj := j.2
  have hi := i.2
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hGm : G.m = D.R.m := rfl
  have hGk : G.k = D.R.k := rfl
  have hGga : G.ga = gap D C := rfl
  have h1 := P.gap_be j
  have e0 : P.b ⟨0, by omega⟩ = (G.b 1 : ℚ) := hb ⟨0, by omega⟩
  have ej : P.b j = (G.b (j.1 + 1) : ℚ) := hb j
  have h2 : P.b ⟨0, by omega⟩ ≤ P.b j := by
    rcases Nat.eq_zero_or_pos j.1 with h0 | hj0
    · exact le_of_eq (congrArg P.b (Fin.ext (by simp [h0])))
    · have := G.b_mono 1 (j.1 + 1) le_rfl (by omega) (by rw [hGm]; omega)
      rw [e0, ej]; exact_mod_cast this.le
  have hu2 := P.u_last_gt (by omega) (by omega)
  have hu1 := P.v_gt_u ⟨D.R.k - 2, by omega⟩
  have hu : P.u ⟨D.R.k - 2 + 1, by omega⟩ = P.u ⟨D.R.k - 1, by omega⟩ :=
    congrArg P.u (Fin.ext (by dsimp only; omega))
  have ev0 : P.v ⟨0, by omega⟩ = (G.v 2 : ℚ) := hv ⟨0, by omega⟩
  have evl : P.v ⟨D.R.k - 2, by omega⟩ = (G.v D.R.k : ℚ) := by
    have := hv ⟨D.R.k - 2, by omega⟩
    dsimp only at this
    rwa [Nat.sub_add_cancel (by omega : 2 ≤ D.R.k)] at this
  have hvv : G.v D.R.k < G.v 2 := G.v_anti 2 D.R.k le_rfl (by omega) (by rw [hGk])
  have hvv' : (G.v D.R.k : ℚ) < G.v 2 := by exact_mod_cast hvv
  rw [hu] at hu1
  rw [evl] at hu1
  have hc : G.mid (D.R.m - i) < (cen D C τ (D.R.m - i) : ℚ) + 1 := Int.lt_floor_add_one _
  have hmid : G.mid (D.R.m - i) = G.a (D.R.m - i) + G.ga / 2 := G.mid_eq (by omega)
  have ha : G.a (D.R.m - i) = (G.v 2 : ℚ) + 1 / 2 + ((i : ℚ) + 1) * (gap D C : ℚ) := by
    simp only [GlobalTheory.SignedHC.GridData.a, hGm, hGga]
    rw [Nat.cast_sub hi.le]; ring
  rw [hmid, ha, hGga] at hc
  have hg := (isLeast_gap D C).1.2.1
  have hN : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have hr : D.R.r + 1 = D.R.k + D.R.m := by unfold Formalism.BasicNotions.Ranks.r; omega
  have m1 : (j.1 + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m2 : j.1 * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m3 : (i.1 + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have m4 : i.1 * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have hrank : rankV D (i.1 + 1) (j.1 + 1) + rankV D i.1 j.1 ≤ 2 * bigN D := by
    unfold rankV bigN; nlinarith
  have hbot : GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j ≤
      rankV D (i.1 + 1) (j.1 + 1) + rankV D i.1 j.1 := by
    unfold GlobalTheory.FunObj.SqNum.botBig GlobalTheory.FunObj.SqNum.botSmall; omega
  have hR : GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j + 1 ≤ gap D C := by omega
  have hR' : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) + 1 ≤ (gap D C : ℚ) := by
    exact_mod_cast hR
  have hpos : (0 : ℚ) ≤ (i : ℚ) * (gap D C : ℚ) := by positivity
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have h0 : (0 : ℚ) ≤ ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) := by positivity
  have key : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) <
      2 * ((num D C τ).e (j + 1) : ℚ) + 2 * (cen D C τ (D.R.m - i) : ℚ) := by
    rw [hne, ← he]
    nlinarith
  have key' : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) <
      2 * ((num D C τ).e (j + 1) + cen D C τ (D.R.m - i)) := by
    have : (((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) : ℚ) <
        ((2 * ((num D C τ).e (j + 1) + cen D C τ (D.R.m - i)) : ℤ) : ℚ) := by
      push_cast; push_cast at key; linarith
    exact_mod_cast this
  exact key'.le

end GlobalTheory.ChiGrid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulRkKChiLatLeRankW
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.CovolRank

theorem comap_val_finite {K B : Type} [Field K] [CommRing B] [Algebra K B] (A : Subalgebra K B)
    (C : Submodule K B) [FiniteDimensional K C] :
    FiniteDimensional K (C.comap A.val.toLinearMap) ∧
      Module.finrank K (C.comap A.val.toLinearMap) ≤ Module.finrank K C := by
  let f : C.comap A.val.toLinearMap →ₗ[K] C :=
    LinearMap.codRestrict C (A.val.toLinearMap ∘ₗ (C.comap A.val.toLinearMap).subtype)
      fun y => Submodule.mem_comap.1 y.2
  have hf : Function.Injective f := fun a b hab => by
    have h := congrArg (fun z : C => (z : B)) hab
    exact Subtype.ext (Subtype.ext h)
  haveI : FiniteDimensional K (C.comap A.val.toLinearMap) := Module.Finite.of_injective f hf
  exact ⟨inferInstance, LinearMap.finrank_le_finrank_of_injective hf⟩

theorem finrank_span_le_of_map {K B : Type} [Field K] [CommRing B] [Algebra K B] (A : Subalgebra K B)
    (C : Submodule K B) (hC : C ≤ Subalgebra.toSubmodule A) {O : Type} [CommRing O] [Module O C]
    (L : Submodule O C) (N : Submodule K A) [FiniteDimensional K N]
    (hL : ∀ F ∈ L, (⟨(F : B), hC F.2⟩ : A) ∈ N) :
    Module.finrank K (Submodule.span K (L : Set C)) ≤ Module.finrank K N := by
  let Φ : C →ₗ[K] A := LinearMap.codRestrict (Subalgebra.toSubmodule A) C.subtype fun y => hC y.2
  have hΦ : Function.Injective Φ := fun a b hab => by
    have h := congrArg (fun z : A => (z : B)) hab
    exact Subtype.ext h
  have hle : Submodule.span K (L : Set C) ≤ N.comap Φ := by
    rw [Submodule.span_le]
    intro F hF
    exact hL F hF
  let ψ : Submodule.span K (L : Set C) →ₗ[K] N :=
    LinearMap.codRestrict N (Φ ∘ₗ (Submodule.span K (L : Set C)).subtype) fun y => hle y.2
  have hψ : Function.Injective ψ := fun a b hab => Subtype.ext (hΦ (congrArg Subtype.val hab))
  exact LinearMap.finrank_le_finrank_of_injective hψ

end GlobalTheory.CovolRank

namespace GlobalTheory.CovolRank

set_option maxHeartbeats 4000000 in
theorem card_mul_rkK_chiLat_le_rankW : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {D : D7} (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (G W : WTZ E), Even G.2 → Even W.2 → KeepsCusp U G → KeepsCusp U W → GoodW U x V dict G → GoodW U x V dict (G + W) → ∀ (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W), (∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) → Fintype.card S * Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ) ≤ rankW U (G + W) := by
  classical
  intro E _ _ _ H Dw l Xo c r U D x V dict S hpq hA G W hG hW hKG hKW hgG hgGW χ u hdet
  have hsec : ∀ G' : WTZ E, cuspW Xo c U G' ≤ Subalgebra.toSubmodule (secRing Xo c) :=
    fun G' f hf => GlobalTheory.LevDesc.mem_secRing (GlobalTheory.AllWt.cuspW_le_secZ G' hf)
  have hfin : ∀ G' : WTZ E, GlobalTheory.AllWt.GoodW U x V dict G' → FiniteDimensional c.F (cuspW Xo c U G') := by
    intro G' hg
    obtain ⟨n, ⟨b, _⟩, _⟩ := hg.1.some
    exact Module.Finite.of_basis b
  have := hfin G hgG
  have := hfin (G + W) hgGW
  obtain ⟨hVs, -⟩ := comap_val_finite (secRing Xo c) (cuspW Xo c U G)
  obtain ⟨hVp, hVp'⟩ := comap_val_finite (secRing Xo c) (cuspW Xo c U (G + W))
  let uR : secRing Xo c := ⟨u, hsec W u.2⟩
  have hact := GlobalTheory.LevDesc.isRightAct_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA
  have hdet' : (Matrix.of fun h g : S => GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA (h * g) uR).det ∈
      nonZeroDivisors (secRing Xo c) := by
    have hc := GlobalTheory.LevDesc.coe_det_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA uR
    refine mem_nonZeroDivisors_iff_left.mpr fun y hy => ?_
    apply Subtype.ext
    have h0 : levDet Xo c S u * (y : Rul Xo c) = 0 := by
      rw [← hc]; exact congrArg Subtype.val hy
    exact hdet _ y.2 h0

  let ι : secRing Xo c →ₗ[c.F] Rul Xo c := (secRing Xo c).val.toLinearMap
  let N : Submodule c.F (secRing Xo c) :=
    (cuspW Xo c U G).comap ι ⊓ GlobalTheory.LevDesc.eigen (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) χ
  have key := (GlobalTheory.finrank_le_card_mul_finrank_eigenspace_le S c.F (secRing Xo c)
    (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) hact.1 hact.2 χ uR hdet'
    ⊥ ((cuspW Xo c U G).comap ι) ((cuspW Xo c U (G + W)).comap ι) N
    (fun h y hy => hKG h _ hy)
    (fun h y hy => by
      rw [Submodule.mem_bot] at hy
      subst hy
      rw [zero_mul]; exact Submodule.zero_mem _)
    (fun h y hy => GlobalTheory.SlopeRec.mul_mem_cuspW hG hW hy (hKW h _ u.2))
    (fun y => Submodule.mem_inf)).2
  have : FiniteDimensional c.F N := Submodule.finiteDimensional_of_le inf_le_left
  have h1 : Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ) ≤ Module.finrank c.F N :=
    finrank_span_le_of_map (secRing Xo c) (cuspW Xo c U G) (hsec G) _ N fun F hF =>
      ⟨F.2, fun h => Subtype.ext (hF.2 h)⟩
  have e : rankW U (G + W) = Module.finrank c.F (cuspW Xo c U (G + W)) := by
    rw [rankW, Formalism.HN.rkK, hgGW.2.2, finrank_top]
  calc Fintype.card S * Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ)
      ≤ Fintype.card S * Module.finrank c.F N := Nat.mul_le_mul_left _ h1
    _ ≤ Module.finrank c.F ((cuspW Xo c U (G + W)).comap ι) := key
    _ ≤ rankW U (G + W) := e ▸ hVp'

end GlobalTheory.CovolRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGaloisStatement
section
open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deepLevelCover_principalLevel_laws_galois : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → Laws D j Y.d.Xo₂ Y.d.c₂ Y.U Y.dict ∧ (letI : Algebra T.Q.c.F Y.d.c₂.F := ((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)).toAlgebra; IsGalois T.Q.c.F Y.d.c₂.F) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ g, Y.Pull f g ↔ Pull Y.d (rulBC Y.hle f) g := by
  first | exact @GlobalTheory.DeepLaws.laws_galois_pull | exact GlobalTheory.DeepLaws.laws_galois_pull | (intros; apply GlobalTheory.DeepLaws.laws_galois_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameSpanCompletedEigenLatticeStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFrame_span_completed_eigenLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) ∧ ∀ v ∈ F.eigLat B.t.act tt, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
  first | exact @GlobalTheory.PtDeg.intFrame_span_eigLat | exact GlobalTheory.PtDeg.intFrame_span_eigLat | (intros; apply GlobalTheory.PtDeg.intFrame_span_eigLat <;> assumption)
end

