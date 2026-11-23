module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductRouteBEqExternalProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelEqUnitNormMulTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallKernel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumB skewGram blkU conjU xiV xiV₁ boxB alpha beta)
open GlobalTheory.RouteSeesaw
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem end_finsupp_sum_apply {α β : Type} (A : Module.End ℂ (β → ℂ)) (Θ : α →₀ ℂ) (f : α → β → ℂ) (w : β) :
    A (fun x => Θ.sum fun d c => c * f d x) w = Θ.sum fun d c => c * A (f d) w := by
  have e : (fun x => Θ.sum fun d c => c * f d x) = ∑ d ∈ Θ.support, Θ d • f d := by
    funext x
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (m + n) := by
  intro a
  have e1 := h a
  have e2 := h' a
  simp only [MonoidHom.div_apply, Circle.coe_div] at *
  rw [e1, e2]
  split_ifs
  · simp
  · have hm : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [div_eq_iff (by simp), add_comm, pow_add, mul_assoc, hm, mul_one]

theorem data_theta_small {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)}
    (hΘ : IsMatched B t ρ i j Θ Θ') : ∀ d ∈ Θ'.support,
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hΘ
  intro d hd
  have hsupp := Finsupp.support_sum hd
  simp only [Finset.mem_biUnion] at hsupp
  obtain ⟨P, -, hP⟩ := hsupp
  have hsupp2 := Finsupp.support_sum hP
  simp only [Finset.mem_biUnion] at hsupp2
  obtain ⟨d', hd', hd'2⟩ := hsupp2
  have hdd := Finset.mem_singleton.1 (Finsupp.support_single_subset hd'2)
  subst hdd
  obtain ⟨h1, h2⟩ := hloc d' hd'
  have v1 := (ρ.vT_is t (i : ℕ) (j : ℕ) i.2.le j.2).2.theta
  have v2 := (ρ.vX_is (i : ℕ) (j : ℕ) i.2 j.2.le).2.theta
  have t1 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h1.2 v1
  have t2 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h2.2 v2
  exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩


set_option maxHeartbeats 1000000 in
theorem seesaw_swapped {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin (spW₁ G i j).rank)
    (e₂ : Fin S'.rank ≃ Fin (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank)
    (hT' : T'.gramᵀ = -((spW₁ G i j).gram.submatrix e₁ e₁))
    (hS' : S'.gram⁻¹ = -((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ.submatrix e₂ e₂))
    (ω : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ))
    (hω : IsWeilDatumO W.ψ S' T' (alpha G t i j / beta G i j) (alpha G t i j) ω)
    (f₁ : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ) (f₂ : WO (G.pS (.chi i j)) (G.pT (.chi i j)) → ℂ)
    (hf₁ : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) f₁)
    (hf₂ : IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) f₂)
    (g : GA D (spV G i j)) (u : GA D (spW₁ G i j)) (g₁ : GA D (spV₁ G i j)) (g' : GA D S') (h' : GA D T')
    (hh : Formalism.L2.Theta.mt T' h' = ((Formalism.L2.Theta.mt _ u).map (cA D)).submatrix e₁ e₁)
    (hg : Formalism.L2.Theta.mt S' g' = ((Formalism.L2.Theta.mt _ (GlobalTheory.SquareComm.blk _ _ (g, g₁))⁻¹).submatrix e₂ e₂)ᵀ) :
    W.kerA (.down t i j) f₁ g u * W.kerA (.right i j) f₂ u g₁ =
      xiV G i j g * xiV₁ G t i j g₁ * ω (g', h') (fun x => box2 f₁ (GlobalTheory.SeesawSmall.adjFn (spW₁ G i j) (spV₁ G i j) f₂)
        (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) ((spW₁ G i j).gram.map (incA D)) :
          Matrix (Fin (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank) (Fin (spW₁ G i j).rank) (AE D))) 0 := by
  have r₁ : T'.rank = (spW₁ G i j).rank := by simpa using Fintype.card_congr e₁
  have r₂ : S'.rank = (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank := by simpa using Fintype.card_congr e₂
  obtain ⟨ωA, hA⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D W.ψ W.ψ_std (spW₁ G i j)
    (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) (alpha G t i j) (alpha G t i j / beta G i j)
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecT hω.hecS (r₁ ▸ hω.resT) (r₂ ▸ hω.resS)
  obtain ⟨hbox, hker⟩ := GlobalTheory.SeesawSmall.seesaw_small hL W t i.2 j.2 ωA hA f₁ f₂ hf₁ hf₂
  rw [hker g u g₁, GlobalTheory.BigSeesaw.swap_eq _ _ S' T' e₁ e₂ hT' hS' hA hω hbox u _ g' h' hh hg]
  rfl


set_option maxHeartbeats 1000000 in
theorem kerSmall_eq_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∀ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB →
    ∃ ξ : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) j)) → ℂ, (∀ x, ‖ξ x‖ = 1) ∧
      ∀ g u, kerSmall W Θ' g g₁ u =
        ξ (g, g₁) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' ΦB (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁)) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv Φ hΦ
  refine ⟨fun x => xiV G i j x.1 * xiV₁ G t i j x.2, fun x => ?_, fun g u => ?_⟩
  · simp only [xiV, xiV₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.flatDet, norm_mul, Circle.norm_coe, mul_one]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.WeilSchrodingerHerm.main D Bs hTr.base _ Γ.V' _ _ hTr.geo.hV'
  obtain ⟨hJ, LS, hLS, h4, h5, h6⟩ := GlobalTheory.WeilSchrodingerSkew.main D Bs hTr.base _ Γ.W _ _ hTr.geo.hW
  have hξ0 : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have eA : Γ.V'.J = (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))).gramᵀ := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; exact (Matrix.transpose_transpose _).symm
  have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
      inv_mul_cancel₀ (neg_ne_zero.2 hξ0), one_smul])
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 •
      (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0))).gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ0, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext a b
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  obtain ⟨ω, hω, -, hth⟩ := GlobalTheory.WeilBridge.exists_theta_eq D Bs hTr.base
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))) Γ.V' Γ.W _ _ _ _
    hTr.geo.hV' hTr.geo.hW eA eB
    Γ.M' hTr.geo.hM' X.α (X.α / X.β) hTr.chars.heckeα (isHecke_div hTr.chars.heckeα hTr.chars.heckeβ) hTr.chars.resα
    (resEtaPow_div hTr.chars.resα hTr.chars.resβ) om' hTr.weil'
  rw [h.ψ, h.α, h.β] at hω
  obtain ⟨g', h', hh', hg'⟩ := GlobalTheory.WeilSchrodinger.match_pair D
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))) Γ.V'.J Γ.W.J (-1) eA eB
    (conjU (spW₁ G i j) (-1) h.JW₁ u) (blkU (spV G i j) (spV₁ G i j) e h.JWW (g, g₁))
  have key := hth _ _ g' h' hh' hg' Φ hΦ.1
  refine Eq.trans ?_ (congrArg (fun z => xiV G i j g * xiV₁ G t i j g₁ * z) key.symm)
  have htr : GlobalTheory.WeilSchrodinger.thetaTr D.host.F Γ.M'.co Bs.ψ Φ =
      fun w => Θ'.sum fun d c => c * boxB e d w := by
    funext w
    show GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho Bs.ψ w Φ) = _
    rw [h.ψ, hΦ.2 w]
    rfl
  refine Eq.trans ?_ (congrArg (fun f => xiV G i j g * xiV₁ G t i j g₁ * ω (g', h') f 0) htr.symm)
  refine Eq.trans ?_ (congrArg (fun z => xiV G i j g * xiV₁ G t i j g₁ * z)
    (end_finsupp_sum_apply (ω (g', h')) Θ' (boxB e) 0).symm)
  rw [kerSmall, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨t1, t2⟩ := data_theta_small W B ρ t i j hΘ d hd
  let e₂ : Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ Fin ((spV G i j).rank + (spV₁ G i j).rank) :=
    e.symm.trans finSumFinEquiv
  have hb : ∀ {R : Type} [CommRing R] (A : Matrix (Fin (spV G i j).rank) (Fin (spV G i j).rank) R)
      (B : Matrix (Fin (spV₁ G i j).rank) (Fin (spV₁ G i j).rank) R),
      (GlobalTheory.Doubling.blkMat finSumFinEquiv A B).submatrix e₂ e₂ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A B := fun A B => by
    ext a b
    simp [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, e₂]
  have hJ' : Γ.W.J = D.host.xi0 • ((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂ := by
    refine h.JWW.trans (congrArg (D.host.xi0 • ·) ?_)
    rw [GlobalTheory.Doubling.gram_hsum, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← hb]
    rfl
  have hT' : (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))).gramᵀ =
      -((spW₁ G i j).gram.submatrix (Equiv.refl _) (Equiv.refl _)) := by
    rw [← eA]
    show Γ.V'.J = -(spW₁ G i j).gram
    rw [h.JW₁, neg_one_smul]
  have hS' : (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0))).gram⁻¹ =
      -(((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    refine e1.trans ?_
    rw [hJ', smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hξ0, neg_one_smul]
  have k := seesaw_swapped hL W t i j
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0)))
    (Equiv.refl (Fin (spW₁ G i j).rank)) e₂ hT' hS' ω hω d.1.2 d.2 t1 t2 g u g₁
    g' h' hh' (by
      rw [hg', ← map_inv, Prod.inv_mk, GlobalTheory.SquareComm.mt_blk]
      exact congrArg transpose (hb (Formalism.L2.Theta.mt _ g⁻¹) (Formalism.L2.Theta.mt _ g₁⁻¹)).symm)
  refine (congrArg (fun z => Θ' d * z) k).trans ?_
  rw [mul_left_comm]
  refine congrArg (fun f => xiV G i j g * xiV₁ G t i j g₁ * (Θ' d * ω (g', h') f 0)) ?_
  funext x
  exact (GlobalTheory.SeesawSmall.thetaSquareProductRouteB_eq_externalProduct e d x).symm

end GlobalTheory.SmallKernel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFactorisationConnectedFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SteinFact

theorem finite_appTop_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}}
    (f : X ⟶ Sp R) [IsProper f] :
    ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom.Finite := by
  letI := GlobalTheory.algebraΓOfHom f
  have h0 := GlobalTheory.ProperFinite.finite_coh_of_isProper f (GlobalTheory.structureModule X) 0
  have h1 := Module.Finite.equiv (GlobalTheory.cohOn.zeroEquiv R (GlobalTheory.structureModule X) ⊤)
  let ρ : GlobalTheory.sectionsOn (GlobalTheory.structureModule X) ⊤ →ₗ[R] Γ(X, ⊤) :=
    { toFun := fun s => (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤ s : Γ(X, ⊤))
      map_add' := fun s t => map_add (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤) s t
      map_smul' := fun r s => by
        rw [GlobalTheory.sectionsOn.toΓ_smul]
        rw [GlobalTheory.restrictGlobal_top]
        rfl }
  have hρ : Function.Bijective ρ := (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤).bijective
  exact Module.Finite.equiv (LinearEquiv.ofBijective ρ hρ)

theorem finite_app_of_isProper {X Y : Scheme.{0}} (g : X ⟶ Y) [IsProper g] {V : Y.Opens}
    (hV : IsAffineOpen V) [IsNoetherianRing Γ(Y, V)] : (g.app V).hom.Finite := by
  let j := (g ⁻¹ᵁ V).ι
  let g' : (g ⁻¹ᵁ V).toScheme ⟶ Sp Γ(Y, V) := g ∣_ V ≫ hV.isoSpec.hom
  have : IsProper g' := inferInstanceAs (IsProper (g ∣_ V ≫ hV.isoSpec.hom))
  have h1 := finite_appTop_of_isProper g'
  have hle : j ''ᵁ ⊤ ≤ g ⁻¹ᵁ V := (g ⁻¹ᵁ V).ι_image_top.le
  have e : (Scheme.ΓSpecIso (.of Γ(Y, V))).inv ≫ g'.appTop = g.appLE V (j ''ᵁ ⊤) hle := by
    ext r
    change (g ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso Γ(Y, V)).inv r) = _
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, ← CommRingCat.comp_apply, Category.assoc,
      Iso.inv_hom_id_assoc, GlobalTheory.ProperFinite.topIso_inv_appTop]
  rw [e] at h1
  have hi : IsIso (X.presheaf.map (homOfLE hle).op) := by
    rw [show homOfLE hle = eqToHom (g ⁻¹ᵁ V).ι_image_top from Subsingleton.elim _ _]
    infer_instance
  exact (RingHom.finite_respectsIso.cancel_right_isIso _ (X.presheaf.map (homOfLE hle).op)).1 h1

theorem stein_factorisation : ∀ (X Y : Scheme.{0}) (g : X ⟶ Y), IsLocallyNoetherian Y → IsProper g → ∃ (Y' : Scheme.{0}) (a : X ⟶ Y') (b : Y' ⟶ Y), a ≫ b = g ∧ IsFinite b ∧ IsProper a ∧ Surjective a ∧ (∀ V : Y'.Opens, Function.Bijective (a.app V).hom) ∧ ∀ y : Y', _root_.IsPreconnected {x : X | a x = y} := by
  intro X Y g hY hg
  have hb : IsFinite g.fromNormalization := by
    refine { toIsAffineHom := inferInstance, finite_app := fun U hU => ?_ }
    have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI := (g.app U).hom.toAlgebra
    have : Module.Finite Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := finite_app_of_isProper g hU
    have : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, g ⁻¹ᵁ U)) :=
      Module.IsNoetherian.finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, g ⁻¹ᵁ U)).toSubmodule
    rw [g.fromNormalization_app hU]
    exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).2 (RingHom.finite_algebraMap.2 this)
  have hY' : IsLocallyNoetherian g.normalization := LocallyOfFiniteType.isLocallyNoetherian g.fromNormalization
  have ha : IsProper g.toNormalization := by
    have : IsProper (g.toNormalization ≫ g.fromNormalization) := by
      rw [g.toNormalization_fromNormalization]; exact hg
    exact IsProper.of_comp _ g.fromNormalization
  have hbij : ∀ V : g.normalization.Opens, Function.Bijective (g.toNormalization.app V).hom := by
    intro V
    refine ⟨g.toNormalization.app_injective V, fun t => ?_⟩
    obtain ⟨s, hs⟩ := GlobalTheory.mem_range_app_of_forall_isAffineOpen g.toNormalization V t fun W hW hWV => by
      have : IsNoetherianRing Γ(g.normalization, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
      exact GlobalTheory.mem_range_toNormalization_app g W _
        (RingHom.IsIntegral.of_finite (finite_app_of_isProper g.toNormalization hW) _)
    exact ⟨s, hs⟩
  have hs : Surjective g.toNormalization := by
    have h := g.toNormalization.denseRange.closure_range
    rw [g.toNormalization.isClosedMap.isClosed_range.closure_eq] at h
    exact ⟨Set.range_eq_univ.mp h⟩
  exact ⟨g.normalization, g.toNormalization, g.fromNormalization, g.toNormalization_fromNormalization, hb, ha, hs,
    hbij, fun y => _root_.GlobalTheory.ZConn.isPreconnected_fibre X _ g.toNormalization hY' ha hbij y⟩

end GlobalTheory.SteinFact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionRationalPointsInvariantTriple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RatInvTheta

theorem inclR_inj (D : D7) : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem sigR_inclR (D : D7) (e : D.host.E) :
    sigR (AF D.host.F) D.sp.cm.sig (inclR (F := D.host.F) (AF D.host.F) e) =
      inclR (F := D.host.F) (AF D.host.F) (D.sp.cm.sig e) := by
  simp [sigR, inclR]

theorem mem_GQ_of {D : D7} (V : HSp D) (g : GA D V) (z : GL (Fin V.rank) D.host.E)
    (hz : mt V g = (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) :
    g ∈ GQ V := by
  refine ⟨z, ?_, Units.ext ?_⟩
  · have hm : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * JR (AF D.host.F) V.gram * mt V g =
        JR (AF D.host.F) V.gram := g.2
    have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig)
        ((z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).map
          (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j; exact sigR_inclR D _
    rw [hz, hcT] at hm
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram
    apply Matrix.map_injective (inclR_inj D)
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul]
    exact hm
  · exact hz.symm

theorem thetaSum_rat_inv : ∀ {D : D7} {a a' : ℕ} (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ γ ∈ ratU D.sp.cm.sig Γ.V.J, ∀ γ' ∈ ratU D.sp.cm.sig Γ.W.J, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin a × Fin (a + a')),
      GlobalTheory.WeilM.thetaSum D.host.F (om (γ, γ') Φ) = GlobalTheory.WeilM.thetaSum D.host.F Φ := by
  intro D a a' Bs Γ X om om' hT γ hγ γ' hγ' Φ hΦ
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.WeilSchrodingerHerm.main D Bs hT.base a Γ.V _ _ hT.geo.hV
  obtain ⟨hJ, L, hL, h4, h5, h6⟩ := _root_.GlobalTheory.WeilSchrodingerSkew.main D Bs hT.base (a + a') Γ.W _ _ hT.geo.hW
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T := GlobalTheory.WeilSchrodinger.hspOf D Γ.V.Jᵀ h1 h2 Γ.V.L hT.geo.hV.lat.toIsLattice h3 (fun _ => (a - Γ.p, Γ.p))
  let S := GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 L hL h6
    (fun _ => (Γ.p + Γ.q, a + a' - (Γ.p + Γ.q)))
  have eA : Γ.V.J = T.gramᵀ := by rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; rfl
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hcW : GlobalTheory.LFun.IsHecke D.host.F D.host.E (X.β / X.α) :=
    ⟨hT.chars.heckeβ.1.div' hT.chars.heckeα.1, fun x => by
      rw [MonoidHom.div_apply, hT.chars.heckeβ.2 x, hT.chars.heckeα.2 x, div_one]⟩
  have rW : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range (X.β / X.α)
      (a + a') := by
    intro x
    have e₁ := hT.chars.resβ x
    have e₂ := hT.chars.resα x
    rw [MonoidHom.div_apply, Circle.coe_div, e₁, e₂, hT.geo.even.neg_one_pow]
    split_ifs
    · simp
    · rcases Nat.even_or_odd a with h | h
      · have h' : Even a' := (Nat.even_add.mp hT.geo.even).mp h
        rw [h.neg_one_pow, h'.neg_one_pow]; simp
      · have h' : Odd a' := by
          rcases Nat.even_or_odd a' with h'' | h''
          · exact absurd ((Nat.even_add.mp hT.geo.even).mpr h'') (Nat.not_even_iff_odd.mpr h)
          · exact h''
        rw [h.neg_one_pow, h'.neg_one_pow]; simp
  obtain ⟨ω, hω, -, hth⟩ := GlobalTheory.WeilBridge.exists_theta_eq D Bs hT.base S T Γ.V Γ.W _ _ _ _ hT.geo.hV hT.geo.hW
    eA eB Γ.M hT.geo.hM X.β (X.β / X.α) hT.chars.heckeβ hcW hT.chars.resβ rW om hT.weil
  obtain ⟨g, h, hh, hg⟩ := GlobalTheory.WeilSchrodinger.match_pair D S T Γ.V.J Γ.W.J (-1) eA eB γ γ'
  obtain ⟨z, hz⟩ := hγ
  obtain ⟨z', hz'⟩ := hγ'
  have hhQ : h ∈ GQ T := by
    refine mem_GQ_of T h z ?_
    rw [hh]
    exact (congrArg Units.val hz).symm
  have hgQ : g ∈ GQ S := by
    have m1 := congrArg Matrix.transpose (Units.mul_inv z')
    have m2 := congrArg Matrix.transpose (Units.inv_mul z')
    rw [Matrix.transpose_mul, Matrix.transpose_one] at m1 m2
    let Z : GL (Fin (a + a')) D.host.E :=
      ⟨((z'⁻¹ : GL (Fin (a + a')) D.host.E) : Matrix (Fin (a + a')) (Fin (a + a')) D.host.E)ᵀ,
        ((z' : GL (Fin (a + a')) D.host.E) : Matrix (Fin (a + a')) (Fin (a + a')) D.host.E)ᵀ, m1, m2⟩
    refine mem_GQ_of S g Z ?_
    rw [hg]
    have h0 : γ'.1 = Matrix.GeneralLinearGroup.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) z' := hz'.symm
    show ((γ'.1)⁻¹ : GL (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))).1ᵀ = _
    rw [h0, ← map_inv]
    rfl
  have hf :=
    _root_.GlobalTheory.ThetaTransformTheta.isThetaFunO_thetaTr D Bs.ψ (_root_.GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hT.base.std) S T Γ.V.J Γ.W.J (-1) eA eB (Fin T.rank × Fin S.rank) Γ.M.co
      hT.geo.hM.rat Φ hΦ
  have key := hth γ γ' g h hh hg Φ hΦ
  have e0 := GlobalTheory.WeilBridge.thetaTr_zero D Γ.M.co Bs.ψ Φ
  have e1 := hω.om_aut g hgQ h hhQ _ hf
  exact key.trans (e1.trans e0)

end GlobalTheory.RatInvTheta
end
end

