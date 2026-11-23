module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumTheta
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstOrtho
section
namespace GlobalTheory.OneMapRef.Kappa

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal GlobalTheory.AdTh.GenConst
open scoped ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ex_eq [Algebra c.F ℂ] {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r} {L : Lt E r} {y : FrPt Xo c ℂ} (A A' : AnFib X bas idx e x L y) :
    A.ex = A'.ex :=
  GlobalTheory.CuspFamilyCompare.exp_unique A.ex_add A'.ex_add A.hol A'.hol (fun j => y.u (e j).1 (e j).2)
    (fun j => by simpa only [Equiv.symm_apply_apply] using A.der (e j))
    (fun j => by simpa only [Equiv.symm_apply_apply] using A'.der (e j))

theorem exists_root {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hmk : IsMark l L mk) {n N : ℕ}
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E} (hY : IsRoots l L mk N Y) {y : Matrix (Fin n) (Fin r) E}
    (hy : ∀ b, (l.M : E) • y b ∈ Mfr l • L) : ∃ q, ∀ b, Y q b - y b ∈ L := by
  have hM0 : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (LevCover.M_pos l).ne'
  choose a ha t ht h using fun b => hmk.surj _ (hy b)
  refine ⟨fun b => Submodule.Quotient.mk (a b), fun b => ?_⟩
  obtain ⟨⟨a', ha', hq, h'⟩, -⟩ := hY (fun b => Submodule.Quotient.mk (a b)) b
  obtain ⟨d, hd⟩ := LevCover.modN_of_mem_both l ((Submodule.Quotient.eq _).1 hq) (Submodule.sub_mem _ ha' (ha b))
  have e₀ : mk a' = mk (a b) + (l.M : E) • mk d := by
    rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← hd, ← map_add (f := _), add_sub_cancel]
  have e₁ : y b = (l.M : E)⁻¹ • mk (a b) + t b := by
    rw [← inv_smul_smul₀ hM0 (y b), h, smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM0]
  rw [e₀, smul_add, inv_smul_smul₀ hM0] at h'
  convert L.sub_mem (L.add_mem h' (hmk.mem d)) (ht b) using 1
  rw [e₁]
  abel

theorem exists_const {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (hr1 : 1 ≤ r) (k : U.Comp) (t : ℝ) (ht : ∀ τ, (U.X k).c τ = t) (n : ℕ) (hn : Even n)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (hs : IsSympl (U.X k) bas)
    (hI : ∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (e j).1) (e j).2)
    (v : TF n g) (hv : IsVac (U.X k) bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v) :
    ∃ C : ℂ, ∀ x : (U.X k).dom, (U.X k).IsOrtho x.1 → letI : Algebra c.F ℂ := σ.toAlgebra
      ∀ (A : AnFib (U.X k) bas idx e x.1 (U.X k).Λ (unC U k x)) (ϑ : (Fin g → ℂ) → ℂ), A.Reads 1 (unC U k x).s ϑ →
        ∀ z : Fin n → Fin g → ℂ, ∏ b, ϑ (z b) = C * thA (U.X k) bas idx v x.1 z := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hC := GlobalTheory.ChartFree.chartIndep
  obtain ⟨W⟩ := nonempty_uw hU
  obtain rfl : g = W.g := Fin.equiv_iff_eq.1 ⟨e.trans W.e.symm⟩
  obtain ⟨-, hL, hmk, -⟩ := uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := ThRead.cmHost_idempotent_trace_eq_one H
  have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun _ => antitone_const, hn⟩
  obtain ⟨Dc, hDe, -⟩ := exists_dic E H Dw l c σ r W.g n (U.X k) 0 e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2 hL hD
  subst hDe
  obtain rfl : idx = Dc.idx := idx_unique hs fun x u j => (hI x u j).trans (Dc.per_eq x u j).symm
  obtain ⟨ρ, hρ, hnorm⟩ := VacNorm.norm_factor_eq E r _ _ bas Dc.idx n hs hn _ hw hw' _ hL v hv
  have hpt : ∀ x (hx : x ∈ (U.X k).dom), IsUnitFr (U.X k) x → ∃ κ : ℂ, ‖κ‖ = ρ ∧
      ∃ (A : AnFib (U.X k) bas Dc.idx Dc.e x (U.X k).Λ (unC U k ⟨x, hx⟩)) (ϑ : (Fin W.g → ℂ) → ℂ),
        A.Marked (W.mark k) ∧ A.Reads 1 (unC U k ⟨x, hx⟩).s ϑ ∧
        IsTheta1 (U.X k) bas Dc.idx (H.w0 : E) x (U.X k).Λ ϑ ∧ MeanOne (U.X k) bas Dc.idx x (U.X k).Λ ϑ ∧
        ∀ z : Fin n → Fin W.g → ℂ, ∏ b, ϑ (z b) = κ * thA (U.X k) bas Dc.idx v x z := by
    intro x hx hux
    obtain ⟨π, hπ⟩ : ∃ π : Fin W.g ≃ Fin W.g, π.trans W.e = Dc.e := ⟨Dc.e.trans W.e.symm, by ext1; simp⟩
    have hπ' : ∀ j, W.e j = Dc.e (π.symm j) := fun j => by rw [← hπ]; simp
    have hid : π.trans (π.symm.trans Dc.idx) = Dc.idx := by ext1; simp
    obtain ⟨A₀, hA₀, ϑ₀, hϑ₀, hm₀⟩ := uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k bas (π.symm.trans Dc.idx) hs
      (fun x u j => by rw [hπ']; exact Dc.per_eq x u _) (fun j => by rw [hπ']; exact Dc.ty_eq _) ⟨x, hx⟩ hux
    have h1 := exists_anFib_trans π A₀
    have hmean := meanOne_trans π hm₀
    rw [hid, hπ] at h1
    rw [hid] at hmean
    obtain ⟨A, hA, hR⟩ := h1
    have hT := isTheta1_of_reads_generator E H Dw l Xo c r _ _ bas Dc.idx Dc.e x _ _ A hs hx hL _ (hR _ hϑ₀)
    obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r _ _ bas Dc.idx n hs hn _ hw hw' _ hL v hv x hx _ hT
    exact ⟨κ, hnorm x hx hux _ κ hT hmean hκ, A, _, hA _ hA₀, hR _ hϑ₀, hT, hmean, hκ⟩
  choose κ hκ hpt using hpt
  obtain ⟨C, -, hCe⟩ := Const.exists_const (U.X k) (Formalism.L2.PjFree.laU U 0 n k) ρ hρ κ hκ
  refine ⟨C, fun x hox A ϑ hϑ => ?_⟩
  have hux : IsUnitFr (U.X k) x.1 := PullbackSections.PfSupAtUnit.dmin_ortho _ hox
  obtain ⟨A₀, ϑ₀, hA₀, -, hT₀, hmean, hprod₀⟩ := hpt x.1 x.2 hux
  have hA : A.Marked (W.mark k) := fun a ha => (hA₀ a ha).trans (congrFun (ex_eq A₀ A) _)
  obtain ⟨κ', hprod⟩ := VacProd.prod_eq_mul_thA E r _ _ bas Dc.idx n hs hn _ hw hw' _ hL v hv x.1 x.2 _
    (isTheta1_of_reads_generator E H Dw l Xo c r _ _ bas Dc.idx Dc.e x.1 _ _ A hs x.2 hL _ hϑ)
  have hM := LevCover.M_pos l
  obtain ⟨-, -, h1, h2, hY⟩ := DualMark.dual_marking E H Dw l r (U.X k) _ (W.mark k) _ hL hmk
    (Complex.isPrimitiveRoot_exp l.M hM.ne')
  obtain ⟨Y, hY⟩ := hY n l.M hM
  have ht0 : 0 < t := by
    obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ (U.X k).Ψ := by
      by_cases h : ComplexEmbedding.conjugate τ₀ ∈ (U.X k).Ψ
      · exact ⟨_, h⟩
      · exact ⟨τ₀, ((U.X k).cmType τ₀).2 h⟩
    rw [← ht ⟨τ, hτ⟩]
    exact mul_pos two_pos (norm_pos_iff.2 ((_root_.map_ne_zero τ).2 (U.X k).ξ0_ne))
  obtain ⟨y, hy, hne⟩ := exists_level_translate_jet_ne_zero E r (U.X k) W.g Dw.p Dc.hr bas Dc.idx n hs hn H.w0 hw' _ hL
    x.1 x.2 hox t ht0 ht (Mfr l) l.M l.odd (by rw [h1, h2]) v hv ϑ₀ _ hT₀ hmean hprod₀ 1 one_ne_zero
    (by rw [MvPolynomial.totalDegree_one]; exact le_trans (by norm_num) l.three_le)
  obtain ⟨q, hq⟩ := exists_root hmk hY hy
  have h3 := right_ne_zero_of_mul (hne _ hq)
  obtain ⟨_, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond E H Dw l Xo c
  have hLaw : Laws := GlobalTheory.allSixLaws.1
  have hP := one_mem_harmA (Dw := Dw) c n
  obtain ⟨f, hf⟩ := (existsUnique_thRule Xo c nab (GlobalTheory.thValTot_of_chartIndep hLaw hC E H Dw l Xo c nab hnab)
    (fun b => levRep (q b)) hP).exists
  have hsec : f ∈ sec Xo c 0 n := GlobalTheory.thetaRule_mem_sec hLaw hC E H Dw l Xo c nab hnab 0 n f ⟨_, _, hP, hf⟩
  have hsb : IsSB (heisG (U.X k) bas (Y q) v) :=
    ((GlobalTheory.SW.heisG_laws E r (U.X k) W.g bas Dc.idx n hs hn).2.2.2 (Y q) v hv.1).1
  have hhol := GlobalTheory.SW.theta_holomorphic_weight E r (U.X k) W.g Dw.p Dc.hr bas Dc.idx n hs hn Dc.k Dc.k'
    _ hsb _ (Dc.mem 1 hP.1)
  have hS := hU.2.2.2.2.1 0 n hD f hsec k
  have hwt : wtOf (U.X k) Dc.hr Dc.k Dc.k' n = Formalism.L2.PjFree.laU U 0 n k := Dc.wt_eq
  rw [hwt] at hhol
  have hval : ∀ x' (hx' : x' ∈ (U.X k).dom)
      (A' : AnFib (U.X k) bas Dc.idx Dc.e x' (U.X k).Λ (unC U k ⟨x', hx'⟩)) (ϑ' : (Fin W.g → ℂ) → ℂ) (κ'' : ℂ),
      A'.Marked (W.mark k) → A'.Reads 1 (unC U k ⟨x', hx'⟩).s ϑ' →
      (∀ z : Fin n → Fin W.g → ℂ, ∏ b, ϑ' (z b) = κ'' * thA (U.X k) bas Dc.idx v x' z) →
      Formalism.L2.PjFree.rdU U f k x' = κ'' * thP (U.X k) Dc.hr bas Dc.idx (heisG (U.X k) bas (Y q) v)
        (MvPolynomial.rename Dc.eL (MvPolynomial.map σ 1)) x' := fun x' hx' A' ϑ' κ'' hA' hϑ' hprod' => by
    have := thVal_eq_thP hC E H Dw l Xo c r W.g (U.X k) bas Dc.idx Dc.e x' _ _ A' hs hx' hL Dw.p n Dc.hr
      Dc.eL hU.1 hn Dc.dir_eq nab hnab ϑ' v _ hϑ' hv hprod' (W.mark k) hmk hA' (fun b => levRep (q b)) (Y q)
      (fun b => by
        obtain ⟨⟨a', ha', hq, hy⟩, hj⟩ := hY q b
        exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1
          (hq.trans (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))).symm), hy⟩, hj⟩) 0 1 hP _
      (ThRead.thValAt_evR hC Xo c nab hnab _ hP hf ℂ (unC U k ⟨x', hx'⟩))
    exact Eq.trans (dif_pos hx') this
  have h4 := hCe _ _ hS.1 hhol.1 (fun x hx b hb => ⟨hS.2.1 x hx b hb, hhol.2.1 x hx b hb⟩)
    (fun x' hx' hu' => by
      obtain ⟨A', ϑ', hA', hϑ', -, -, hprod'⟩ := hpt x' hx' hu'
      exact hval x' hx' A' ϑ' _ hA' hϑ' hprod') x.1 x.2
  rw [hval x.1 x.2 A ϑ κ' hA hϑ hprod, map_one, map_one] at h4
  rw [← mul_right_cancel₀ h3 h4]
  exact hprod

end GlobalTheory.OneMapRef.Kappa

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

theorem GlobalTheory.OneMapRef.exists_const_ortho : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (k : U.Comp) (t : ℝ), (∀ τ, (U.X k).c τ = t) → ∀ n : ℕ, Even n → ∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X k) bas → Matched c σ (U.X k) idx e → ∀ v : TF n g, IsVac (U.X k) bas (H.w0 : D.host.E) (tens (stdL D.host.E n) (U.X k).Λ) v → ∃ C : ℂ, ∀ x : (U.X k).dom, (U.X k).IsOrtho x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (A : AnFib (U.X k) bas idx e x.1 (U.X k).Λ (ptC U k x)) (th : (Fin g → ℂ) → ℂ), A.Reads 1 (ptC U k x).s th → ∀ z : Fin n → Fin g → ℂ, ∏ b, th (z b) = C * thA (U.X k) bas idx v x.1 z := by
  intro D H Dw l Xo c σ r U hσ hU hr _ k t ht n hn g bas idx e hs hm v hv
  exact GlobalTheory.OneMapRef.Kappa.exists_const (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hr k t ht n hn bas idx e hs hm.1 v hv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsDetAtUnram
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.DetUnit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem det_mem_intAE (V : HSp D) (g : GA D V)
    (h : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V),
      finMat D.sp.cm.sig V.gram g *ᵥ y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)) :
    finPart D (Formalism.L2.Theta.mt V g).det ∈ intAE D := by
  obtain ⟨L, hL, hfg, hsp⟩ := GlobalTheory.SplitHeckeLabel.exists_coord_lattice V
  have hd : finPart D (Formalism.L2.Theta.mt V g).det = (finMat D.sp.cm.sig V.gram g).det :=
    RingHom.map_det (finPart D) (Formalism.L2.Theta.mt V g)
  rw [hd, GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]
  rw [← hL] at h
  exact GlobalTheory.DetTranslate.det_mem_int D.host.F L _ hfg hsp h

theorem part_mem_intAE {e d : AE D} (he : e * e = e) (hd : finPart D d ∈ intAE D) :
    finPart D (e * d + (1 - e)) ∈ intAE D := by
  have h1 : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he])
  have h2 : finPart D (1 - e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul]; congr 1; linear_combination he)
  rw [RingHom.map_add (f := _), RingHom.map_mul]
  exact add_mem (GlobalTheory.SplitHeckeLabel.mul_mem_intA h1 hd) h2

theorem exists_isDetAt_unram : ∀ (D : D7) (V : HSp D) (ε : AF D.host.F) (e : AE D), IsSplitIdem D e → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → ∀ g ∈ KsphC V ∅, ∃ x, IsDetAt e V g x ∧ ∀ χ : (AE D)ˣ →* Circle, UnramAt ε χ → χ x = 1 := by
  intro D V ε e he hε g hg
  obtain ⟨h1, h0, -⟩ := he
  have hm : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hd : (Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, hm, Matrix.det_one]
  have hf : finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g⁻¹ = 1 := by
    change (finHom V g).1 * (finHom V g⁻¹).1 = 1
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have i1 := det_mem_intAE V g fun y hy => (hg.2.1 y).1 hy
  have i2 := det_mem_intAE V g⁻¹ fun y hy => (hg.2.1 _).2 (by rw [Matrix.mulVec_mulVec, hf, Matrix.one_mulVec]; exact hy)
  generalize (Formalism.L2.Theta.mt V g⁻¹).det = d' at hd i2
  have hx : (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) * (e * d' + (1 - e)) = 1 := by
    linear_combination e * e * hd + (2 - (Formalism.L2.Theta.mt V g).det - d') * h1
  refine ⟨⟨_, _, hx, (mul_comm _ _).trans hx⟩, rfl, fun χ hχ => hχ _ ?_ (part_mem_intAE h1 i1) (part_mem_intAE h1 i2)⟩
  rw [← hε]
  change (e + cA D e) * (e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1
  linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * h1 + ((Formalism.L2.Theta.mt V g).det - 1) * h0

end GlobalTheory.Mem.DetUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalUnitaryEquivRowStageCompat
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace GlobalTheory.Mem.R3.RowStdRat

open GlobalTheory.Mem.R3.RowAd GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem ptE_eq (X : Stages) (h : Bridge.Gf X.toD7.sp.X') :
    ptE X h = LiftBrg.castGL (rank_X' X) (Formalism.UG.bc (swapAE X.toD7) h.1) := rfl

def psiX (X : Stages) (hg : X.toD7.sp.X'.gram = 1) :
    Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) →* GQ X.toD7.sp.X' where
  toFun γ :=
    have hm : LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E) ∈
        Formalism.UG.UJ (X.toD7.sp.cm.sig : X.toD7.host.E →+* X.toD7.host.E) X.toD7.sp.X'.gram := by
      rw [hg]
      exact castGL_mem_UJ_one _ _ _ γ.2
    ⟨(show GA X.toD7 X.toD7.sp.X' from
        (⟨Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F))
            (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E)),
          bc_inclR_mem_HR _ _ _ _ hm⟩ : HR (AF X.toD7.host.F) X.toD7.sp.cm.sig X.toD7.sp.X'.gram)),
      Subgroup.mem_subgroupOf.2 ⟨_, hm, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_one]; rfl) | (simp <;> rfl)))
  map_mul' a b := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_mul]; rfl) | (simp <;> rfl)))

theorem psiX_mat (X : Stages) (hg : X.toD7.sp.X'.gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1)) :
    matHom X.toD7.sp.X' (psiX X hg γ : GA X.toD7 X.toD7.sp.X') =
      Formalism.UG.bc (incA X.toD7) (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E)) := rfl

theorem ptE_ratF_psiX (X : Stages) (hg : X.toD7.sp.X'.gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1)) :
    ptE X (Bridge.ratF X.toD7.sp.X' (psiX X hg γ)) = (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) γ).1 := by
  rw [ptE_eq, Formalism.L2.Col.ratIn_val]
  have e1 : ((Bridge.ratF X.toD7.sp.X' (psiX X hg γ)) : GL (Fin X.toD7.sp.X'.rank) _) =
      Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F))
        (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E)) := by
    change finHom X.toD7.sp.X' _ = _
    rw [finHom, MonoidHom.comp_apply, Subgroup.coe_subtype, psiX_mat]
    exact GlobalTheory.HLatMove.bc_map_bc_inclR _ _
  rw [e1]
  have e2 : Formalism.UG.bc (swapAE X.toD7) (Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F))
      (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E))) =
      Formalism.UG.bc (Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E)
        (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E)) := by
    ext a b
    simp [Formalism.UG.bc, swapAE, inclR, Formalism.UG.inclE]
  rw [e2, ← castGL_bc, castGL_symm_castGL']

end GlobalTheory.Mem.R3.RowStdRat

namespace GlobalTheory.Mem.R3.RowStdRat

open GlobalTheory.Mem.R3.RowAd GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem psiX_injective (X : Stages) (hg : X.toD7.sp.X'.gram = 1) : Function.Injective (psiX X hg) := by
  intro a b hab
  have h2 : (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) a).1 = (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) b).1 := by
    rw [← ptE_ratF_psiX X hg a, ← ptE_ratF_psiX X hg b, hab]
  simp only [Formalism.L2.Col.ratIn_val] at h2
  exact Subtype.ext (Formalism.L2.DIV.incl_inj _ _ _ h2)

theorem psiX_surjective (X : Stages) (hg : X.toD7.sp.X'.gram = 1) : Function.Surjective (psiX X hg) := by
  intro δ
  obtain ⟨γE, hγE, e⟩ := Subgroup.mem_subgroupOf.1 δ.2
  have hγ : LiftBrg.castGL (rank_X' X) γE ∈ Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) := by
    rw [hg] at hγE
    exact castGL_mem_UJ_one _ _ _ hγE
  refine ⟨⟨_, hγ⟩, Subtype.ext (Subtype.ext ?_)⟩
  change Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F))
    (LiftBrg.castGL (rank_X' X).symm (LiftBrg.castGL (rank_X' X) γE)) = _
  rw [castGL_symm_castGL' (rank_X' X) γE]
  exact e

theorem matEq_castGL {A : Type} [CommRing A] {m n : ℕ} (h : m = n) (x : GL (Fin m) A) : MatEq (LiftBrg.castGL h x) x := by
  subst h
  refine ⟨rfl, fun i j i' j' hi hj => ?_⟩
  have hi' : i = i' := Fin.ext hi
  have hj' : j = j' := Fin.ext hj
  subst hi' hj'
  simp [LiftBrg.castGL, Matrix.reindexAlgEquiv_apply]

theorem stdRat_equiv : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok →
    ∀ (e : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* Bridge.Gf X.toD7.sp.X'),
    (∀ x, RowAd.ptE X (e x) = x.1) →
    ∃ eΓ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* GQ X.toD7.sp.X',
      (∀ γ, Bridge.ratF X.toD7.sp.X' (eΓ γ) = e (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) γ)) ∧
      ∀ γ, ∃ γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E, Bridge.IsRatMat X.toD7.sp.X' (eΓ γ) γE ∧
        MatEq γE γ.1 := by
  intro X px I hI e he
  have hg := RowDeco.gram_X'_eq_one X I hI
  have hinj : Function.Injective (ptE X) := by
    intro h h' hh
    obtain ⟨x, rfl⟩ := e.surjective h
    obtain ⟨x', rfl⟩ := e.surjective h'
    rw [he, he] at hh
    rw [Subtype.ext hh]
  refine ⟨MulEquiv.ofBijective (psiX X hg) ⟨psiX_injective X hg, psiX_surjective X hg⟩, fun γ => ?_, fun γ => ?_⟩
  · apply hinj
    rw [he]
    exact ptE_ratF_psiX X hg γ
  · exact ⟨LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E), psiX_mat X hg γ,
      matEq_castGL _ _⟩

end GlobalTheory.Mem.R3.RowStdRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelConjBaseLatticeUnitary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem exists_stepLevel_conj : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (b : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), b ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ v, bc (prV (E := E) v) b ∈ levelVL σ J v S.Lb) → (∀ v, (T : 𝓞 F) ∈ v.asIdeal → (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = S.Uloc v) → (∀ v, v ∉ bad → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) → ∃ S' : StepLevel F E σ J T f bad, S'.Lb = S.Lb ∧ S'.U = S.U.map (MulAut.conj b).toMonoidHom ∧ ∀ (x : S'.U) (z : S.U), x.1 = b * z.1 * b⁻¹ → S'.chi x = S.chi z := by
  intro F E _ _ _ _ _ σ n J T f bad S b hb hlev hT hone
  classical
  let eqv := Subgroup.equivMapOfInjective S.U (MulAut.conj b).toMonoidHom
    (fun x y h => (MulAut.conj b).injective h)
  have heqv : ∀ z : S.U, ((eqv z : S.U.map (MulAut.conj b).toMonoidHom) : GL (Fin n) _) = b * z.1 * b⁻¹ := fun z => rfl
  have hbc : ∀ v (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), bc (prV (E := E) v) (b⁻¹ * x * b) =
      (bc (prV (E := E) v) b)⁻¹ * bc (prV (E := E) v) x * bc (prV (E := E) v) b := fun v x => by
    rw [map_mul, map_mul, map_inv]
  have hP : ∀ x, b⁻¹ * x * b ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ↔ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := fun x => by
    constructor
    · intro h
      have e2 : b * (b⁻¹ * x * b) * b⁻¹ = x := by group
      rw [← e2]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb h) (Subgroup.inv_mem _ hb)
    · intro h
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) h) hb
  let S' : StepLevel F E σ J T f bad :=
    { Lb := S.Lb
      Lb_fin := S.Lb_fin
      Lb_span := S.Lb_span
      Lb_int := S.Lb_int
      Lb_dual := S.Lb_dual
      Lb_index := S.Lb_index
      Uloc := fun v => (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom
      Uloc_le := by
        intro v
        rintro _ ⟨y, hy, rfl⟩
        have hbv : bc (prV (E := E) v) b ∈ UPts σ J (v.adicCompletion F) := (hlev v).1
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbv (S.Uloc_le v hy)) (Subgroup.inv_mem _ hbv)
      Uloc_lev := by
        intro v
        rintro _ ⟨y, hy, rfl⟩
        have hbv := hlev v
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbv (S.Uloc_lev v hy)) (Subgroup.inv_mem _ hbv)
      Uloc_hyp := by
        intro v hv hTv
        show (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = levelVL σ J v S.Lb
        ext x
        rw [mem_map_conj, hone v hv hTv, inv_one, one_mul, mul_one, S.Uloc_hyp v hv hTv]
      fM := S.fM
      fM_acg := S.fM_acg
      fM_mod := S.fM_mod
      fT := S.fT
      fT_ne := S.fT_ne
      fT_T := S.fT_T
      fM_card := S.fM_card
      fT_L := S.fT_L
      UlocAlt := by
        intro v h
        show (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = _
        rw [hT v h]
        exact S.UlocAlt v h
      U := S.U.map (MulAut.conj b).toMonoidHom
      U_eq := by
        intro x
        rw [mem_map_conj, S.U_eq, hP]
        refine and_congr_right fun _ => forall_congr' fun v => ?_
        rw [hbc v x]
        exact (mem_map_conj _ _ _).symm
      U_compact := by
        letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
        letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
        haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
        haveI : Module.Finite (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          Module.Finite.equiv (Algebra.TensorProduct.commRight F (FiniteAdeleRing (𝓞 F) F) E).toLinearEquiv
        haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
        haveI : IsTopologicalRing (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) _
        have hc : Continuous (fun x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => b * x * b⁻¹) :=
          (continuous_const.mul continuous_id).mul continuous_const
        have := S.U_compact.image hc
        convert this using 1
        rw [Subgroup.coe_map]
        rfl
      U_open := by
        letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
        letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
        haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
        haveI : Module.Finite (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          Module.Finite.equiv (Algebra.TensorProduct.commRight F (FiniteAdeleRing (𝓞 F) F) E).toLinearEquiv
        haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
        haveI : IsTopologicalRing (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) _
        haveI : ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
          inferInstanceAs (ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)).toSubmonoid)
        let b' : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨b, hb⟩
        have hc : Continuous (fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => b'⁻¹ * x * b') :=
          (continuous_const.mul continuous_id).mul continuous_const
        have := S.U_open.preimage hc
        convert this using 1
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_map_conj]
        rfl
      chi := S.chi.comp eqv.symm.toMonoidHom
      chi_triv := by
        intro x hx
        show S.chi (eqv.symm x) = 1
        apply S.chi_triv
        intro v hv
        have e1 : ((eqv.symm x : S.U) : GL (Fin n) _) = b⁻¹ * x.1 * b := by
          have h2 := heqv (eqv.symm x)
          rw [MulEquiv.apply_symm_apply] at h2
          rw [h2]
          group
        rw [e1, hbc v, hx v hv, mul_one, inv_mul_cancel] }
  refine ⟨S', rfl, rfl, fun x z hxz => ?_⟩
  show S.chi (eqv.symm x) = S.chi z
  congr 1
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (hxz.trans (heqv z).symm)

end GlobalTheory.Mem.Col2.ChEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemPrimeOfInclEMemPlaceIdealIntegralAdelicSpanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_prime_of_inclE_mem_placeIdealIntegralAdelicSpan : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (α : 𝓞 D.host.E), Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E)) ∈ GlobalTheory.Mem.SymChar.wInt X w → α ∈ w.asIdeal := by
  first | exact @GlobalTheory.Mem.SymChar.mem_of_inclE_mem_wInt | exact GlobalTheory.Mem.SymChar.mem_of_inclE_mem_wInt | (intros; apply GlobalTheory.Mem.SymChar.mem_of_inclE_mem_wInt <;> assumption)
end

