module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0147
public import Formalism.LocalRingCardinality.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveTopMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.Core.Rk.TopOnto

open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift GlobalTheory.Core.Rk.Top.Model GlobalTheory.PointAtPlaceHom Formalism.MainNotions.StandardLattice Matrix

section General

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  have hG : IsUnit (gramAt D V τ) := by
    rw [← M.fr_gram τ]
    exact (((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self (M.ε τ)))).mul (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  obtain ⟨u, rfl⟩ : IsUnit g := isUnit_of_mul_isUnit_right (hg'.symm ▸ hG : IsUnit (gᴴ * gramAt D V τ * g))
  exact Submodule.subset_span
    (Formalism.IndefR.SchurOrthogonalityAlt.smoothVec_rep M τ ⟨u, hg⟩ (Formalism.IndefR.SchurOrthogonalityAlt.gp_sv_of_mem hw))

theorem real_induction (hθ : IsInfFam θ) (P : GA D V → Prop) (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (hat : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), P (atTau θ V τ g)) : ∀ a ∈ GinfC V, P a := by
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have key : ∀ s : Finset D.what₂.Tau, ∀ a ∈ GinfC V, (∀ τ ∉ s, infMat D.sp.cm.sig V.gram (θ τ) a = 1) → P a := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a ha h
      rw [R.2.2.1 a ha 1 (one_mem _) fun τ => by rw [h τ (Finset.notMem_empty τ), infMat_one]]
      exact h1
    | insert τ s hτ ih =>
      intro a ha h
      have hg := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a τ
      have hb := atTau_spec hθ V τ hg
      have hi : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a))⁻¹ *
          infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a)) = 1 := fun ρ => by
        rw [← infMat_mul, inv_mul_cancel, infMat_one]
      rw [← mul_inv_cancel_left (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a)) a]
      refine hmul _ _ (hat τ _ hg) (ih _ (mul_mem (inv_mem hb.1) ha) fun ρ hρ => ?_)
      rw [infMat_mul]
      by_cases c : ρ = τ
      · subst c
        have := hi ρ
        rwa [hb.2.1] at this
      · have := hi ρ
        rw [hb.2.2 ρ c] at this
        rw [h ρ (by simp [c, hρ])]
        exact this
  exact fun a ha => key Finset.univ a ha fun τ h => absurd (Finset.mem_univ τ) h

theorem multT_rel {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} (v v' : M.Vec) (x x' : GA D V) (c : ℂ)
    (h : ∀ m, IsMultMap θ M J χ m → m v' x' = c * m v x) {T} (hT : T ∈ MultT θ M J χ) :
    T (PiTensorProduct.tprod ℂ v') x' = c * T (PiTensorProduct.tprod ℂ v) x := by
  obtain ⟨m, hm, rfl⟩ := hT
  show PiTensorProduct.lift m _ x' = c * PiTensorProduct.lift m _ x
  rw [PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
  induction hm using Submodule.span_induction with
  | mem m hm => exact h m hm
  | zero => simp
  | add a b _ _ ha hb => simp only [MultilinearMap.add_apply, Pi.add_apply, ha, hb, mul_add]
  | smul r a _ ha => simp only [MultilinearMap.smul_apply, Pi.smul_apply, ha, smul_eq_mul]; ring

theorem multT_rel' {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} (x x' : GA D V) (c : ℂ)
    (h : ∀ m, IsMultMap θ M J χ m → ∀ v, m v x' = c * m v x) {T} (hT : T ∈ MultT θ M J χ) (v : SmT M) :
    T v x' = c * T v x := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, multT_rel v v x x' c (fun m hm => h m hm v) hT, smul_eq_mul, smul_eq_mul]
    ring
  | add a b ha hb => rw [map_add (f := _), Pi.add_apply, Pi.add_apply, ha, hb, mul_add]

theorem exists_ratPt (hθ : IsInfFam θ) {n : ℕ} (hn : V.rank = n) (δ : GL (Fin n) D.host.E)
    (hδ : δ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn))) :
    ∃ γ ∈ GQ V, finN V hn γ = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ ∧
      ∀ τ, (infN θ V hn (Equiv.refl _) γ τ : Matrix (Fin n) (Fin n) ℂ) = (δ : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) := by
  subst hn
  have hm : Formalism.UG.bc (incA D) δ ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram :=
    unit_transfer (Equiv.refl _) (incA D) (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig)
      (fun _ => rfl) V.gram _ (fun _ _ => rfl) δ.1 _ (fun _ _ => rfl) hδ
  refine ⟨⟨_, hm⟩, ⟨δ, hδ, rfl⟩, rfl, fun τ => ?_⟩
  exact Matrix.ext fun i j => (hθ τ).1 _

theorem infN_eq {n : ℕ} (hn : V.rank = n) (γ : GA D V) (τ : D.what₂.Tau) :
    (infN θ V hn (Equiv.refl _) γ τ : Matrix (Fin n) (Fin n) ℂ) =
      (infMat D.sp.cm.sig V.gram (θ τ) γ).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  rfl

end General

section Law

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}


set_option maxHeartbeats 1000000 in
theorem real_translate (hθ : IsInfFam θ) (hj : IsJ u M j) : ∀ a ∈ GinfC D.sp.X', ∀ v : SmT M, ∃ v' : SmT M,
    lT _ (infPt θ a) (j v') = j v ∧ ∀ T ∈ MultT θ M J χ, ∀ h, T v' h = T v (h * a) := by
  refine real_induction hθ _ (fun v => ⟨v, by rw [map_one, lT_one], fun T _ h => by rw [mul_one]⟩) (fun a b ha hb v => ?_)
    fun τ g hg v => ?_
  · obtain ⟨v₁, e1, f1⟩ := hb v
    obtain ⟨v₂, e2, f2⟩ := ha v₁
    refine ⟨v₂, by rw [map_mul (infPt θ), lT_mul, e2, e1], fun T hT h => ?_⟩
    rw [f2 T hT, f1 T hT, mul_assoc]
  · induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      let w : M.sm τ := ⟨M.rep τ g (v τ), rep_mem_sm M τ hg _ (v τ).2⟩
      refine ⟨r • PiTensorProduct.tprod ℂ (Function.update v τ w), ?_, fun T hT h => ?_⟩
      · rw [map_smul, map_smul, map_smul]
        congr 1
        funext y
        refine hj.eqv τ g hg v w rfl _ y fun ρ => ?_
        refine (congrArg (· * y.1 ρ) (infN_atTau θ _ (rankP D) hθ τ hg ρ)).trans ?_
        by_cases c : ρ = τ
        · subst c
          simp only [Function.update_self]
        · simp only [Function.update_of_ne c, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
      · rw [map_smul, map_smul, Pi.smul_apply, Pi.smul_apply,
          multT_rel v (Function.update v τ w) (h * atTau θ _ τ g) h 1 (fun m hm => by
            rw [one_mul]; exact congrFun (hm.equiv τ g hg v w rfl) h) hT, one_mul]
    | add a b ha hb =>
      obtain ⟨a', e1, f1⟩ := ha
      obtain ⟨b', e2, f2⟩ := hb
      refine ⟨a' + b', by rw [map_add j, map_add j, map_add, e1, e2], fun T hT h => ?_⟩
      rw [map_add T, map_add T, Pi.add_apply, Pi.add_apply, f1 T hT, f2 T hT]

theorem hasMat_finPt {h : GA D D.sp.X'} (hh : h ∈ GfC D.sp.X') : HasMat h (finPt h).1 :=
  ⟨hh, fun i j => (finN_apply D.sp.X' (rankP D) h (finCongr (rankP D) i) (finCongr (rankP D) j)).symm⟩

end Law

section Form

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}

end Form

end GlobalTheory.Core.Rk.TopOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionLemmaOfWittCoreDescent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem transvTrivial_of_descent (D : D7) (hD : Descent D) : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvTrivial D := by
  intro S S₀ T ρ d ψ χS χT om hom μ 𝓕 hμ a v hv u hu x hx f hf
  obtain ⟨om₀, hom₀⟩ := (hD ψ S T χS χT om hom).1 S₀ ρ d
  obtain ⟨m, b, c, rfl, hdet, hk⟩ := _root_.GlobalTheory.Unf.transv_eq_levi_nB_nC D S S₀ ρ d _ v hv u hu
  obtain ⟨h1, h2, h3⟩ := hk T x hx
  have F := fun g hg => _root_.GlobalTheory.MixSourceFormulas.mixed_source D ψ S S₀ T ρ d χS χT om om₀ hom hom₀ μ 𝓕 hμ g hg
  have hc := hom.om_pres (d.nC c, 1) f hf
  have hb := hom.om_pres (d.nB b, 1) _ hc
  have e : om (d.levi m * d.nB b * d.nC c, 1) f = om (d.levi m, 1) (om (d.nB b, 1) (om (d.nC c, 1) f)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      mul_one, mul_one]
  have hq : symplOH S T (d.extX T x) (d.extY T (x ⬝ c.1)) = 0 := h3
  rw [e]
  change I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d T ψ μ 𝓕 _ x = I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d T ψ μ 𝓕 f x
  rw [(F _ hb).levi, h1, (F _ hc).unip, h2, GlobalTheory.MixPer.heisO_zero, (F _ hf).centre, hq, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, hdet]
  simp

theorem transvLemma_of_descent : ∀ D : D7, Descent D → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvLemma D := fun D hD =>
  ⟨(_root_.GlobalTheory.TransvAdelic.transv_unitary_conj D).1, (_root_.GlobalTheory.TransvAdelic.transv_unitary_conj D).2, transvTrivial_of_descent D hD⟩

end GlobalTheory.Unf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeyl
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Gen
open GlobalTheory.StdUnn.Model
variable {D : D7} {n : ℕ}

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : ∃ a b c d, M = blk4 a b c d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  rw [blk4, Matrix.fromBlocks_toBlocks]
  ext i j
  simp

theorem rel {g : G D n} {a b c d : Mx D n n} (hg : mat g = blk4 a b c d) :
    -(adj c * a) + adj a * c = 0 ∧ -(adj c * b) + adj a * d = 1 ∧ -(adj d * b) + adj b * d = 0 := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rw [JR_Jst, hg] at h
  simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, mul_zero, mul_one, add_zero, zero_add, mul_neg, neg_mul] at h
  exact ⟨(blockMatrixTwoByTwoFin_injective h).1, (blockMatrixTwoByTwoFin_injective h).2.1, (blockMatrixTwoByTwoFin_injective h).2.2.2⟩

variable {S : Subgroup (G D n)}
  (hm : ∀ (g : G D n) (a : GL (Fin n) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → g ∈ S)
  (hn : ∀ (g : G D n) (b : Mx D n n), mat g = blk4 1 b 0 1 → g ∈ S)
  (hw : ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S)

include hm hn in
theorem mem_of_upper {g : G D n} {a b d : Mx D n n} (hg : mat g = blk4 a b 0 d) (ha : IsUnit a) : g ∈ S := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨m, hmm⟩ := exists_levi (D := D) (n := n) u⁻¹
  have h1 : (adj u.1 : Mx D n n) * d = 1 := by simpa using (rel hg).2.1
  rw [← S.mul_mem_cancel_left (hm m _ hmm)]
  refine hn _ ((u⁻¹).1 * b) ?_
  rw [mat_mul, hmm, hg, submatrix_fromBlocks_mul]
  simp only [inv_inv, Units.inv_mul, mul_zero, zero_mul, add_zero, zero_add, h1]

include hm hn hw in
theorem mem_of_lower {g : G D n} {a c d : Mx D n n} (hg : mat g = blk4 a 0 c d) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨w, hww⟩ := exists_weyl (D := D) (n := n)
  rw [← S.mul_mem_cancel_left (hw w hww), ← S.mul_mem_cancel_right (hw w hww)]
  refine mem_of_upper hm hn (a := -d) (b := c) (d := -a) ?_ hd.neg
  rw [mat_mul, mat_mul, hww, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

include hm hn hw in
theorem mem_of_isUnit {g : G D n} {a b c d : Mx D n n} (hg : mat g = blk4 a b c d) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨u, rfl⟩ := hd
  have adj_mul_local {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
      adj (x * y) = adj y * adj x := by
    unfold adj
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have h1 : (adj u.1 : Mx D n n) * b = adj b * u.1 := neg_add_eq_zero.1 (rel hg).2.2
  have h2 : (adj (u⁻¹).1 : Mx D n n) * adj u.1 = 1 := by rw [← adj_mul_local, Units.mul_inv, adj_one]
  have h3 : (adj (-(b * (u⁻¹).1)) : Mx D n n) = -(b * (u⁻¹).1) := by
    rw [adj_neg, adj_mul_local]
    congr 1
    calc (adj (u⁻¹).1 : Mx D n n) * adj b = adj (u⁻¹).1 * (adj b * u.1) * (u⁻¹).1 := by
          rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
      _ = b * (u⁻¹).1 := by rw [← h1, ← mul_assoc, h2, one_mul]
  obtain ⟨x, hx⟩ := (exists_unip _).2 h3
  rw [← S.mul_mem_cancel_left (hn x _ hx)]
  refine mem_of_lower hm hn hw (a := a + -(b * (u⁻¹).1) * c) (c := c) (d := u.1) ?_ u.isUnit
  rw [mat_mul, hx, hg, submatrix_fromBlocks_mul]
  simp only [one_mul, zero_mul, zero_add, neg_mul, mul_assoc, Units.inv_mul, mul_one, add_neg_cancel]

end GlobalTheory.StdUnn.Gen

namespace GlobalTheory.StdUnn

theorem eq_top_of_levi_unip_weyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (GlobalTheory.StdUnn.G D n)), (∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 a.1 0 0 (GlobalTheory.MixModel.adj (a⁻¹).1) → g ∈ S) → (∀ (g : GlobalTheory.StdUnn.G D n) (b : Mx D n n), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 1 b 0 1 → g ∈ S) → (∀ g : GlobalTheory.StdUnn.G D n, GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 → g ∈ S) → S = ⊤ := by
  intro D n S hm hn hw
  rw [eq_top_iff]
  intro g _
  obtain ⟨a, b, c, d, hg⟩ := Gen.exists_blockMatrixTwoByTwoFin_eq (mat g)
  obtain ⟨p', p, q', q, hi⟩ := Gen.exists_blockMatrixTwoByTwoFin_eq (mat g⁻¹)
  have h1 : mat g * mat g⁻¹ = 1 := by rw [← Gen.mat_mul, mul_inv_cancel]; rfl
  rw [hg, hi, Model.submatrix_fromBlocks_mul, ← Model.block_matrix_one] at h1
  obtain ⟨x, hx, hu⟩ := GlobalTheory.HermTransversal.exists_herm_isUnit D n c d p q (Model.blockMatrixTwoByTwoFin_injective h1).2.2.2
  obtain ⟨y, hy⟩ := (Model.exists_unip x).2 hx
  rw [← S.mul_mem_cancel_right (hn y _ hy)]
  refine Gen.mem_of_isUnit hm hn hw (a := a) (b := a * x + b) (c := c) (d := c * x + d) ?_ hu
  rw [Gen.mat_mul, hg, hy, Model.submatrix_fromBlocks_mul]
  simp only [mul_one, mul_zero, add_zero]

end GlobalTheory.StdUnn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValueZeroParabolic
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.SiegelLaw

theorem value_zero_parabolic : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → ∀ (Φ : schwartzA θ V.rank n), ∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g : G D n, (ω (p * g) Φ).1 0 = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (s0 V n + (n : ℂ) / 2) * (ω g Φ).1 0 := by
  intro D n V ψ χ θ μ ω hω Φ p hp a ha g
  obtain ⟨m, v, b, e, hm, hv⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hp a ha
  have e' : ω (p * g) Φ = ω m (ω v (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ((0 : Mx D V.rank n) * a.1 : Mx D V.rank n) = 0 := Matrix.zero_mul _
  have z2 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by
    rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  have hs : s0 V n + (n : ℂ) / 2 = (V.rank : ℂ) / 2 := by rw [s0]; ring
  rw [e', hω.levi m _ hm, z1, hω.unip v b hv, z2, hs]
  simp [halfTr]

end GlobalTheory.StdUnn.SiegelLaw
end

