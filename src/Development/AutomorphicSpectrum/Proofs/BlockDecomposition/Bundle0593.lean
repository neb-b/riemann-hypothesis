module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1334
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0343
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0393
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0571
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0354
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0431
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0503
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalStabilizerProperty
section
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

theorem mt_decomp_j0 (c : skewA D t) (b : Mx D t W.rank) (g : GA D W) (a : GL (Fin t) (AE D)) :
    mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) ⬝ d.j0 = (d.j0 + d.jX ⬝ b) ⬝ mt W g := by
  have e : mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) =
      mt B (d.nC c) ⬝ (mt B (d.nB b) ⬝ (mt B (d.emb0 g) ⬝ mt B (d.levi a))) := by
    simp only [mt_mul, Matrix.mul_assoc]
  have e₁ : mt B (d.emb0 g) ⬝ mt B (d.levi a) ⬝ d.j0 = d.j0 ⬝ mt W g := by
    rw [Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  have e₂ : mt B (d.nC c) ⬝ (d.j0 + d.jX ⬝ b) = d.j0 + d.jX ⬝ b := by
    rw [Matrix.mul_add, d.nC_j0, ← Matrix.mul_assoc, d.nC_jX]
  rw [e, Matrix.mul_assoc, Matrix.mul_assoc, e₁, ← Matrix.mul_assoc (mt B (d.nB b)), d.nB_j0,
    ← Matrix.mul_assoc, e₂]

theorem mt_decomp_jY (c : skewA D t) (g : GA D W) (a : GL (Fin t) (AE D)) :
    mt B (d.nC c * (d.emb0 g * d.levi a)) ⬝ d.jY = (d.jY + d.jX ⬝ c.1) ⬝ adj (a⁻¹).1 := by
  have e : mt B (d.nC c * (d.emb0 g * d.levi a)) = mt B (d.nC c) ⬝ (mt B (d.emb0 g) ⬝ mt B (d.levi a)) := by
    simp only [mt_mul]
  have e₁ : mt B (d.emb0 g) ⬝ mt B (d.levi a) ⬝ d.jY = d.jY ⬝ adj (a⁻¹).1 := by
    rw [Matrix.mul_assoc, d.levi_jY, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclY]
  rw [e, Matrix.mul_assoc, e₁, ← Matrix.mul_assoc, d.nC_jY]

theorem coordB_eq_zero (c : skewA D t) (b : Mx D t W.rank) (g : GA D W) (a : GL (Fin t) (AE D))
    (h : d.pX ⬝ mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) ⬝ d.j0 = 0) : b = 0 := by
  rw [Matrix.mul_assoc, mt_decomp_j0, ← Matrix.mul_assoc, Matrix.mul_add, d.pX_j0, ← Matrix.mul_assoc,
    d.pX_jX, Matrix.one_mul, zero_add] at h
  have e : mt W g ⬝ mt W g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  calc b = b ⬝ mt W g ⬝ mt W g⁻¹ := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem coordC_eq_zero (c : skewA D t) (g : GA D W) (a : GL (Fin t) (AE D))
    (h : d.pX ⬝ mt B (d.nC c * (d.emb0 g * d.levi a)) ⬝ d.jY = 0) : c = 0 := by
  rw [Matrix.mul_assoc, mt_decomp_jY, ← Matrix.mul_assoc, Matrix.mul_add, d.pX_jY, ← Matrix.mul_assoc,
    d.pX_jX, Matrix.one_mul, zero_add] at h
  have e : adj (a⁻¹).1 ⬝ adj a.1 = 1 := by rw [← adj_mul, Units.mul_inv, adj_one]
  apply Subtype.ext
  calc c.1 = c.1 ⬝ adj (a⁻¹).1 ⬝ adj a.1 := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem pX_levM {q : GlobalTheory.RegSW.stab d} (hq : q ∈ levM d) :
    d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0 ∧ d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0 := by
  obtain ⟨g, a, h⟩ := hq
  rw [h, mt_mul]
  constructor
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_projX_anisotropicEmbedding, d.pX_j0]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jY, ← Matrix.mul_assoc (mt B (d.emb0 g)), d.wittDecomp_anisotropicEmbedding_inclY,
      ← Matrix.mul_assoc, d.pX_jY, Matrix.zero_mul]

theorem mem_levM_of_pX {q : GlobalTheory.RegSW.stab d} (h₀ : d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0)
    (hY : d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0) : q ∈ levM d := by
  obtain ⟨n, ⟨c, b, hn⟩, m, ⟨g, a, hm⟩, e⟩ := exists_radN_mul_levM d q
  have hq : (q : GA D B) = d.nC c * d.nB b * (d.emb0 g * d.levi a) := by
    rw [e, Subgroup.coe_mul, hn, hm]
  rw [hq] at h₀ hY
  have hb := coordB_eq_zero d c b g a h₀
  subst hb
  rw [d.nB_zero, mul_one] at hY
  have hc := coordC_eq_zero d c g a hY
  subst hc
  refine (mem_levM d).2 ⟨g, a, hq.trans ?_⟩
  rw [d.nC_zero, d.nB_zero, one_mul, one_mul]

theorem isClosed_levM (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) :
    IsClosed (levM d : Set (GlobalTheory.RegSW.stab d)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : Continuous fun q : GlobalTheory.RegSW.stab d => mt B (q : GA D B) :=
    (continuous_mt B).comp continuous_subtype_val
  have h₀ : IsClosed {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0} :=
    isClosed_eq ((continuous_const.matrix_mul hc).matrix_mul continuous_const) continuous_const
  have hY : IsClosed {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0} :=
    isClosed_eq ((continuous_const.matrix_mul hc).matrix_mul continuous_const) continuous_const
  have e : (levM d : Set (GlobalTheory.RegSW.stab d)) = {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0} ∩
      {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0} :=
    Set.ext fun q => ⟨fun h => pX_levM d h, fun h => mem_levM_of_pX d h.1 h.2⟩
  rw [e]
  exact h₀.inter hY

end GlobalTheory.CompanionTheory.QKAvg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitAlmostEverywhereFacts
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.UnitAEPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem eventually_one (hU : Unr E) (n : ℕ) (δ : GL (Fin n) E)
    (hP : (δ * thE E n δ).val.charpoly.Separable) :
    ∀ᶠ w : Pl E in cofinite, locEl n w δ ∈ GlobalTheory.LFun.KGL w (n := n) ∧
      (∀ g : GLw n w, g⁻¹ * locEl n w δ * thL n w g ∈ GlobalTheory.LFun.KGL w (n := n) →
        ∃ t ∈ twCent (thL n w) (locEl n w δ), t⁻¹ * g ∈ GlobalTheory.LFun.KGL w (n := n)) ∧
      ∀ t ∈ twCent (thL n w) (locEl n w δ),
        IsCompact (closure (Subgroup.zpowers t : Set (GLw n w))) → t ∈ GlobalTheory.LFun.KGL w (n := n) := by
  filter_upwards [_root_.GlobalTheory.BCT.SepBezout.bezout_eventually E _ hP, GlobalTheory.BCT.GoodInt.eventually_mem_KGL δ,
    GlobalTheory.BCT.GoodInt.eventually_mem_KGL (δ * thE E n δ)] with w hgood hd hN
  obtain ⟨-, hinv, hKθ, -, -, -, -, -, hchar, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  have hy : locEl n w δ ∈ GlobalTheory.LFun.KGL w (n := n) := by
    unfold locEl
    split_ifs
    · exact hN
    · exact hd
  have hgood' : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w (locEl n w δ)).val.charpoly + v * derivative (nrmL n w (locEl n w δ)).val.charpoly = 1 := by
    rw [hchar δ]; exact hgood
  have hNK : nrmL n w (locEl n w δ) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    unfold nrmL
    split_ifs with hs
    · exact hy
    · have h2 : thetaGL n (cj w) (locEl n w δ) = thL n w (locEl n w δ) := by
        unfold thL; rw [if_neg hs]
      rw [h2]; exact mul_mem hy (hKθ _ hy)
  refine ⟨hy, fun g hg => ?_, fun t ht hc => ?_⟩
  · by_cases hs : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w (locEl n w δ) = locEl n w δ := by unfold nrmL; rw [if_pos hs]
      rw [hn1] at hgood'
      rw [hθ1] at hg ⊢
      obtain ⟨t, ht, k, hk, rfl⟩ := GlobalTheory.T.integral_conj_etale_mem_centralizer_mul_integralGL E n w _ g hy hgood' hg
      exact ⟨t, ht, by simpa using hk⟩
    · obtain ⟨t, ht, k, hk, rfl⟩ := GlobalTheory.T.inert_integral_twistedConjugates_twistedCentralizer_mul_maxCompact E hU n w hs _ g hy hgood' hg
      exact ⟨t, ht, by simpa using hk⟩
  · refine GlobalTheory.T.mem_maxCompactGL_of_commute_etale_charpoly_bounded E n w (nrmL n w (locEl n w δ)) t hNK hgood' ?_ hc
    have ht' : t * locEl n w δ = locEl n w δ * thL n w t := ht
    by_cases hs : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w (locEl n w δ) = locEl n w δ := by unfold nrmL; rw [if_pos hs]
      rw [hn1]; rw [hθ1] at ht'; simpa using ht'
    · have hn1 : nrmL n w (locEl n w δ) = locEl n w δ * thL n w (locEl n w δ) := by
        unfold nrmL; rw [if_neg hs]; unfold thL; rw [if_neg hs]
      rw [hn1]
      calc t * (locEl n w δ * thL n w (locEl n w δ))
          = locEl n w δ * thL n w t * thL n w (locEl n w δ) := by rw [← mul_assoc, ht']
        _ = locEl n w δ * thL n w (t * locEl n w δ) := by simp only [map_mul, mul_assoc]
        _ = locEl n w δ * thL n w (locEl n w δ * thL n w t) := by rw [ht']
        _ = locEl n w δ * thL n w (locEl n w δ) * t := by simp only [map_mul, hinv, mul_assoc]

theorem isCompact_fst {A B : Type} [Group A] [TopologicalSpace A] [T2Space A] [Group B] [TopologicalSpace B]
    [IsTopologicalGroup A] [IsTopologicalGroup B] (t : A × B)
    (h : IsCompact (closure (Subgroup.zpowers t : Set (A × B)))) :
    IsCompact (closure (Subgroup.zpowers t.1 : Set A)) := by
  refine (h.image continuous_fst).closure_of_subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem isCompact_snd {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B] [T2Space B]
    [IsTopologicalGroup A] [IsTopologicalGroup B] (t : A × B)
    (h : IsCompact (closure (Subgroup.zpowers t : Set (A × B)))) :
    IsCompact (closure (Subgroup.zpowers t.2 : Set B)) := by
  refine (h.image continuous_snd).closure_of_subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem main : PositivityTheory.Rg.BcB.G8.Fin.UnitAE := by
  intro E _ _ _ hU a b S _ δ₁ δ₂ h₁ h₂
  have e₁ := eventually_one hU a δ₁ h₁.2.2.1
  have e₂ := eventually_one hU b δ₂ h₂.2.2.1
  have hT : Tendsto (Subtype.val : {w : Pl E // w ∈ S} → Pl E) cofinite cofinite :=
    Subtype.val_injective.tendsto_cofinite
  filter_upwards [hT.eventually e₁, hT.eventually e₂] with w hw₁ hw₂ y hy
  subst hy
  obtain ⟨i₁, u₁, c₁⟩ := hw₁
  obtain ⟨i₂, u₂, c₂⟩ := hw₂
  refine ⟨⟨i₁, i₂⟩, fun g hg => ?_, (Subgroup.closure_le _).2 ?_⟩
  · obtain ⟨t₁, ht₁, k₁⟩ := u₁ g.1 hg.1
    obtain ⟨t₂, ht₂, k₂⟩ := u₂ g.2 hg.2
    refine ⟨(t₁, t₂), ?_, ⟨k₁, k₂⟩⟩
    exact Prod.ext ht₁ ht₂
  · rintro t ⟨ht, hc⟩
    have ht' : t * _ = _ * _ := ht
    exact ⟨c₁ t.1 (congrArg Prod.fst ht') (isCompact_fst t hc), c₂ t.2 (congrArg Prod.snd ht') (isCompact_snd t hc)⟩

end GlobalTheory.CompanionTheory.UnitAEPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedProductIrreducible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSeg.Unlinked

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def subIncl (π : Representation ℂ (GL (Fin N) k) V) (S : Subrepresentation π) :
    S.toRepresentation.IntertwiningMap π where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' := fun _ => rfl

def quotProj {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V)
    (σ : Representation ℂ (GL (Fin N) k) W) (f : σ.IntertwiningMap π) :
    π.IntertwiningMap (GlobalTheory.CompanionTheory.BZSeg.TwoSeg.quotRep π σ f) where
  toLinearMap := (LinearMap.range f.toLinearMap).mkQ
  isIntertwining' := fun _ => rfl

theorem isIrreducible_of_generic {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (π : Representation ℂ (GL (Fin N) k) V) [Nontrivial V] (hπ : IsSmooth π)
    (hr : Module.rank ℂ (TwJacquet π (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (hsub : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W)
      (f : σ.IntertwiningMap π), Function.Injective f → Nontrivial W → IsGeneric σ)
    (hquo : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin N) k) W)
      (f : π.IntertwiningMap τ), Function.Surjective f → Nontrivial W → IsGeneric τ) :
    π.IsIrreducible := by
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro e
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h2 : v ∈ (⊤ : Subrepresentation π).toSubmodule := trivial
    rw [← e] at h2
    exact hv h2
  haveI : Nontrivial (Subrepresentation π) := ⟨⟨⊥, ⊤, hbt⟩⟩
  refine ⟨fun S => ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨hb, ht⟩ := hc
  have hinj : Function.Injective (subIncl π S) := Subtype.val_injective
  have hSn : Nontrivial S.toSubmodule := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    refine hb (Subrepresentation.toSubmodule_injective ?_)
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    exact congrArg Subtype.val (Subsingleton.elim (⟨v, hv⟩ : S.toSubmodule) 0)
  have hrange : LinearMap.range (subIncl π S).toLinearMap = S.toSubmodule := Submodule.range_subtype _
  have hQn : Nontrivial (V ⧸ LinearMap.range (subIncl π S).toLinearMap) := by
    refine Submodule.Quotient.nontrivial_iff.2 ?_
    rw [hrange]
    intro e
    exact ht (Subrepresentation.toSubmodule_injective e)
  have hσ := hsub _ S.toRepresentation (subIncl π S) hinj hSn
  exact GlobalTheory.CompanionTheory.BZSeg.TwoSeg.not_isGeneric_quotRep hψ h1 π _ (subIncl π S) hinj hπ hr hσ
    (hquo _ _ (quotProj π _ (subIncl π S)) (Submodule.mkQ_surjective _) hQn)

end GlobalTheory.CompanionTheory.BZSeg.Unlinked

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredity
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier

theorem whitHeredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    WhitHeredity k := by
  intro k _ _ _ _ ψ hψ hψ1 h N d hd X _ _ π hπ
  obtain ⟨J, hJs, hJ⟩ := _root_.GlobalTheory.CompanionTheory.Rodier.OpenCoinv.openFns_whittaker k ψ hψ h N d hd (piTensor π) (isSmooth_piTensor hπ)
  obtain ⟨E⟩ := _root_.GlobalTheory.CompanionTheory.Rodier.PiCoinv.twJacquet_piTensor_equiv π (fun a => unipB k (Fin (d a))) (fun a => whitChar ψ (d a))
  set T := twKer (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N) with hT
  set S := twKer (piTensor π) (unipM k d) (whitM d ψ) with hS
  let a : openFns d hd (piTensor π) →ₗ[ℂ] (IndSp (stdBlocks d hd) (piTensor π)) ⧸ T :=
    T.mkQ ∘ₗ (openFns d hd (piTensor π)).subtype
  let b : openFns d hd (piTensor π) →ₗ[ℂ] (⨂[ℂ] a, X a) ⧸ S := S.mkQ ∘ₗ J
  have ha : Function.Surjective a := by
    intro y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨f₀, h0, h1⟩ := _root_.GlobalTheory.CompanionTheory.Rodier.exists_open_congr k ψ hψ hψ1 h N d hd (piTensor π) f
    refine ⟨⟨f₀, h0⟩, ?_⟩
    exact ((Submodule.Quotient.eq T).2 (by simpa [neg_sub] using T.neg_mem h1))
  have hb : Function.Surjective b := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨f, rfl⟩ := hJs w
    exact ⟨f, rfl⟩
  have hker : LinearMap.ker a = LinearMap.ker b := by
    ext f
    simp only [a, b, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.subtype_apply]
    exact (hJ f).symm
  exact ⟨(a.quotKerEquivOfSurjective ha).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans ((b.quotKerEquivOfSurjective hb).trans E))⟩

end GlobalTheory.CompanionTheory.Rodier
end

