module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.HermitianForms.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Interlace
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0416
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplitting
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TuplePrimedSpaceClassesLevelAndComparison
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastAllTranspose
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.Col2.LowerTie

section Gen
open Formalism.L2.Forms
variable {ι : Type} [Fintype ι] {N n : ℕ}

theorem lastAll_transpose (a : ι → ℂˣ) (τ : ι) :
    (((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))ᵀ = ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
  ext i j
  simp only [Matrix.transpose_apply, lastAll, lastGL_apply]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem fnOf_lastAll (G : ι → Matrix (Fin N) (Fin N) ℂ) (lam : ι → DomWeight N) (a : ι → ℂˣ) (P : Pol ℂ ι N) :
    fnOf G (shiftOf lam) (fun τ => ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) P =
      fnOf G (shiftOf lam) 1 (actP lam (lastAll N a) P) := by
  have h := fnOf_mul G (shiftOf lam) (fun τ => ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) 1 P
  simp only [Pi.one_apply, mul_one] at h
  rw [h]
  refine congrArg (fnOf G (shiftOf lam) 1) ?_
  have e : trAct (lastAll N a) = Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) := by
    unfold trAct
    simp only [lastAll_transpose]
  simp only [actP, detTwK, detPow, shiftOf, LinearMap.smul_apply, AlgHom.toLinearMap_apply, e]
  refine congrArg (· • _) (Finset.prod_congr rfl fun τ _ => ?_)
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]

theorem scalar_last (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (h : ∀ i, 0 ≤ Br.bBr hN lam sg i) (a : ℂˣ) :
    (a : ℂ) ^ (-Br.nBr lam sg) * ((a : ℂ) ^ lam.detShift * ∏ s, (a : ℂ) ^ (Br.bBr hN lam sg s).toNat) = 1 := by
  subst hN
  have ha : (a : ℂ) ≠ 0 := a.ne_zero
  have e : ∏ s, (a : ℂ) ^ (Br.bBr rfl lam sg s).toNat = (a : ℂ) ^ (∑ s, Br.bBr rfl lam sg s) := by
    have : ∀ s, (a : ℂ) ^ (Br.bBr rfl lam sg s).toNat = (a : ℂ) ^ (Br.bBr rfl lam sg s) := fun s => by
      rw [← zpow_natCast, Int.toNat_of_nonneg (h s)]
    simp only [this]
    induction (Finset.univ : Finset (Fin n)) using Finset.cons_induction with
    | empty => simp
    | cons x s hx ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ ha, ih]
  have e2 : Br.nBr lam sg = lam.detShift + ∑ s, Br.bBr rfl lam sg s := by
    simp only [Br.nBr, Br.bBr, DomWeight.detShift, Finset.sum_sub_distrib, Fin.sum_univ_castSucc]
    simp [Br.iC]
    change ∑ i : Fin n, lam.w i.castSucc + lam.w (Fin.last n) - ∑ i, sg.w i = lam.w (Fin.last n) + (∑ x : Fin n, lam.w x.castSucc - ∑ i, sg.w i)
    ring
  rw [e, ← zpow_add₀ ha, ← zpow_add₀ ha, e2]
  simp

theorem branchingProjection_act_last (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (h : ∀ τ i, 0 ≤ Br.bBr hN (lam τ) (sg τ) i) (a : ι → ℂˣ) (P : Pol ℂ ι N) :
    (∏ τ, (a τ : ℂ) ^ (-Br.nBr (lam τ) (sg τ))) • (Br.brStdP hN lam sg (actP lam (lastAll N a) P) : Pol ℂ ι n) =
      (Br.brStdP hN lam sg P : Pol ℂ ι n) := by
  rw [branchingProjection_last, smul_smul]
  have e : (∏ τ, (a τ : ℂ) ^ (-Br.nBr (lam τ) (sg τ))) * (detTwK lam (lastAll N a) * ∏ τ, ∏ s, (a τ : ℂ) ^ Br.bExp hN lam sg τ s) = 1 := by
    have h2 : detTwK lam (lastAll N a) = ∏ τ, (a τ : ℂ) ^ (lam τ).detShift := by
      simp only [detTwK, detPow, lastAll, det_lastGL' hN, Units.val_zpow_eq_zpow_val]
    rw [h2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    exact scalar_last hN (lam τ) (sg τ) (h τ) (a τ)
  rw [e, one_smul]
end Gen
end GlobalTheory.Mem.Col2.LowerTie

namespace GlobalTheory.Mem.Col2.LowerTie

section Rec
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

theorem embT_eq : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
  funext τ
  ext y
  show B.host.φ₀ _ = _
  rw [← B.embE_φ₀]
  rfl

include l in
theorem pi_mul_star : ((X.piT u : 𝓞 B.host.E) : B.host.E) * star ((X.piT u : 𝓞 B.host.E) : B.host.E) = (B.T u : B.host.E) := by
  have h := congrArg (fun z : 𝓞 B.fields.E => (z : B.fields.E)) (l.pr.piT_norm u)
  simp only [map_mul, map_natCast] at h
  exact h

include l in
theorem star_pi_ne : star ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := (l.per u I.mu0).tz_ne

theorem bZ_std (hO : I.Ok) (hP : TC.Pins B X) (z0 : Fin (B.R.N B.R.m) → B.host.E)
    (hz : ∀ j, z0 j = if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) :
    bZ (D := I.rec7 l Z) u z0 =
      Matrix.diagonal fun i : Fin (B.R.N B.R.m) => if i.1 + 1 = B.R.N B.R.m then (star ((X.piT u : 𝓞 B.host.E) : B.host.E))⁻¹ else 1 := by
  have hc := (spaces_in_coordinates I hO hP l Z).2.2.1
  have hπ := pi_mul_star I l u
  have h0 := star_pi_ne I l u
  have hp0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := fun h => h0 (by rw [h, star_zero])
  refine Matrix.ext fun (a b : Fin (B.R.N B.R.m)) => ?_
  have ha := a.2
  have hb := b.2
  rw [Matrix.diagonal_apply]
  by_cases h : b.1 < B.R.N B.R.m - 1
  · have e : bZ (D := I.rec7 l Z) u z0 a b = iXc (I.rec7 l Z) (Pi.single ⟨b.1, h⟩ 1) a := by
      exact (dif_pos h).trans (LinearMap.toMatrix'_apply _ _ _)
    refine (e.trans (hc _ a)).trans ?_
    by_cases hab : a = b
    · subst hab
      rw [dif_pos h, if_pos rfl, if_neg (by omega)]
      exact Pi.single_eq_same (M := fun _ : Fin (B.R.N B.R.m - 1) => B.host.E) _ _
    · rw [if_neg hab]
      split_ifs with h2
      · exact Pi.single_eq_of_ne (M := fun _ : Fin (B.R.N B.R.m - 1) => B.host.E) (fun h3 => hab (Fin.ext (Fin.mk.inj_iff.1 h3))) _
      · rfl
  · have e : bZ (D := I.rec7 l Z) u z0 a b = z0 a / (B.T u : B.host.E) := by
      exact dif_neg h
    rw [e, hz, ← hπ]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos (by omega), if_pos (by omega)]
      field_simp
    · rw [if_neg hab, if_neg (fun h3 => hab (Fin.ext (by omega))), zero_div]

def aT (τ : Tau B.R) : ℂˣ :=
  Units.mk0 (embAt B.embLL B.fields.emb τ (star ((X.piT u : 𝓞 B.host.E) : B.host.E))) ((map_ne_zero _).2 (star_pi_ne I l u))

theorem mZ_std (hO : I.Ok) (hP : TC.Pins B X) (z0 : Fin (B.R.N B.R.m) → B.host.E)
    (hz : ∀ j, z0 j = if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) :
    mZ (D := I.rec7 l Z) u z0 =
      fun τ => ((lastAll (B.R.N B.R.m) (aT I l u) τ : GL (Fin (B.R.N B.R.m)) ℂ) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ) := by
  have h0 := star_pi_ne I l u
  have e : (bZ (D := I.rec7 l Z) u z0)⁻¹ =
      Matrix.diagonal fun i : Fin (B.R.N B.R.m) => if i.1 + 1 = B.R.N B.R.m then star ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1 := by
    rw [bZ_std I l Z u hO hP z0 hz]
    refine Matrix.inv_eq_left_inv (A := Matrix.diagonal fun i : Fin (B.R.N B.R.m) =>
      if i.1 + 1 = B.R.N B.R.m then (star ((X.piT u : 𝓞 B.host.E) : B.host.E))⁻¹ else 1) ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs
    · exact mul_inv_cancel₀ h0
    · exact mul_one 1
  funext τ
  refine Matrix.ext fun (a b : Fin (B.R.N B.R.m)) => ?_
  have e2 : mZ (D := I.rec7 l Z) u z0 τ a b = embAt B.embLL B.fields.emb τ ((Matrix.diagonal fun i : Fin (B.R.N B.R.m) =>
      if i.1 + 1 = B.R.N B.R.m then star ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) a b) := by
    unfold mZ
    rw [e, embT_eq]
    rfl
  rw [e2]
  simp only [lastAll, lastGL_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [aT]

end Rec
end GlobalTheory.Mem.Col2.LowerTie

namespace GlobalTheory.Mem.Col2.LowerTie

theorem lowerMap_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (u : B.Word) (Ch : ℕ → Type) (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf),
    I.StdF l Z u F → ∀ (ψ : ((I.rec7 l Z).mem u).P.Wz) (c : ((I.rec7 l Z).fm u).clsP)
      (P : MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m) × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m)) ℂ),
      (∀ s, F.eWz ψ c s = fnOf _ (shiftOf (Formalism.L2.Forms.lamT u (I.rec7 l Z).R.m)) (mZ u F.til.z0) P
        ((F.val (I.rec7 l Z).R.m le_rfl (Or.inr rfl)).eY s)) →
      F.valP.eW (((I.rec7 l Z).mem u).P.lowerMap ψ) c =
        fnOf _ (shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen (I.rec7 l Z) u P) := by
  intro B X I hO hP l Z u Ch chOf F hS ψ c P hψ
  have hl : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u = B.wts.lamTrue u B.R.m := funext (trueWeight_lastStep_trueColumns I l Z u)
  have hs : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u = B.wts.sgTrue := funext (trueRowWeight_trueColumns I l Z u)
  have hl' : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u (I.rec7 l Z).R.m = B.wts.lamTrue u B.R.m := hl
  have hs' : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = B.wts.sgTrue := hs
  have hI : ∀ τ i, 0 ≤ Br.bBr (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ) i := by
    intro τ i
    have h := (Formalism.MainNotions.product_first_zeroth_parts.interlaceTr (I.rec7 l Z) u (sg_interlace F.valP) τ i).1
    rw [hl, hs] at h
    exact sub_nonneg.2 h
  have h1 : ψ c = fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) 1
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P) := by
    refine Eq.trans ?_ (fnOf_lastAll (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (B.wts.lamTrue u B.R.m) (aT I l u) P)
    funext s
    have h := hψ s
    rw [hS.eWz, hl', mZ_std I l Z u hO hP _ hS.z0] at h
    refine h.trans ?_
    have h2 := hS.eY B.R.m le_rfl (Or.inr rfl) s
    exact congrArg (fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) _ P) (Subtype.ext h2)
  have h3 : polOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)) (ψ c) =
      actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P := by
    have e : (fun τ => ((Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
    have h := polOf_fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m))
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P)
    rw [e] at h
    rw [h1]
    exact h
  have h4 : Formalism.L2.Ker.brTen (I.rec7 l Z) u P = (Br.brStdP (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P : Pol ℂ (Tau B.R) (B.R.N B.R.m - 1)) := by
    have h := blk_brOne (ι := Tau B.R) (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P
    refine Eq.trans ?_ h
    unfold Formalism.L2.Ker.brTen
    rw [hl, hs]
    rfl
  have h5 := branchingProjection_act_last (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue hI (aT I l u) P
  funext s
  rw [hS.eW _ c s ⟨s.1, s.2⟩ rfl, hs', h4, ← h5, ← h3]
  rfl

end GlobalTheory.Mem.Col2.LowerTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormHeckeEigen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.Equivar


open CategoryTheory MonObj in
theorem marked_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) {mk mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : A.Marked mk) (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk' a = mk a + l.M • u) :
    A.Marked mk' := by
  intro a ha
  obtain ⟨u, hu, e'⟩ := hc a ha
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  rw [h a ha, e', smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM, hadd, A.ex_add,
    (A.ex_ker _).2 ⟨u, hu, rfl⟩, _root_.mul_one]

variable {D : D7} {S T : HSp D} {r g g' : ℕ}

theorem latW_injective (hr : T.rank = r) : Function.Injective (latW (D := D) (T := T) hr) := by
  subst hr
  intro L L' h
  ext v
  exact SetLike.ext_iff.1 h v

theorem sameSp_of_isSet {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {hr : T.rank = r} {X X' : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {eT' : D.what₂.Tau ≃ X'.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
    {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} (h : IsSet ψ θ S T hr X eT bas) (h' : IsSet ψ θ S T hr X' eT' bas')
    (hp : X'.p0 = X.p0) : SameSp X' X := by
  obtain ⟨-, -, -, -, hm, hk, he, -⟩ := h
  obtain ⟨-, -, -, -, hm', hk', he', -⟩ := h'
  refine ⟨?_, hm'.1.trans hm.1.symm, hp, hm'.2.trans hm.2.symm, hk'.trans hk.symm⟩
  ext τ
  constructor
  · intro hτ
    obtain ⟨ρ, hρ⟩ := eT'.surjective ⟨τ, hτ⟩
    have : τ = (eT ρ).1 := by rw [he, ← he', hρ]
    exact this ▸ (eT ρ).2
  · intro hτ
    obtain ⟨ρ, hρ⟩ := eT.surjective ⟨τ, hτ⟩
    have : τ = (eT' ρ).1 := by rw [he', ← he, hρ]
    exact this ▸ (eT' ρ).2

theorem symm_eq_of_isSet {X X' : Data D.host.E r} {eT : D.what₂.Tau ≃ X.Ψ} {eT' : D.what₂.Tau ≃ X'.Ψ}
    (he : ∀ ρ, (eT ρ).1 = tauE D ρ) (he' : ∀ ρ, (eT' ρ).1 = tauE D ρ) (τ : D.host.E →+* ℂ) (h : τ ∈ X.Ψ)
    (h' : τ ∈ X'.Ψ) : eT'.symm ⟨τ, h'⟩ = eT.symm ⟨τ, h⟩ := by
  rw [Equiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [he', ← he, Equiv.apply_symm_apply]

theorem exists_real_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {hr : T.rank = r} {X : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (h : IsSet ψ θ S T hr X eT bas)
    (idx : Fin g ≃ X.Ψ × Fin r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {L : Lt D.host.E r} {th : (Fin g → ℂ) → ℂ}
    (hm : MeanOne X bas idx x L th) : ∃ w : WO S T, Ker.IsRealPt w ∧
      Ker.gaussR X bas idx x (Ker.zR X idx x (rePt θ hr eT w)) * ∏ b, th (Ker.zR X idx x (rePt θ hr eT w) b) ≠ 0 := by
  obtain ⟨-, hθ, -, hev, -, -, -, hs⟩ := h
  obtain ⟨z, hz⟩ : ∃ z, th z ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨_, _, -, -, h3⟩ := hm
    simp [hc] at h3
  have hq : X.p0 + (r - X.p0) = r := by have := X.p0_le; omega
  obtain ⟨⟨Lz, hL⟩, -⟩ := GlobalTheory.Ker.zR_laws _ r X g _ hq bas idx S.rank hs hev x hx
  obtain ⟨v, hv⟩ := Lz.surjective fun _ => z
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hw : rePt θ hr eT (Matrix.of fun a k => σ fun ρ => v (eT ρ) k (Fin.cast hr a) : WO S T) = v := by
    funext τ k a
    have := hσ.comp (fun ρ => v (eT ρ) k (Fin.cast hr (Fin.cast hr.symm a))) (eT.symm τ)
    refine this.trans ?_
    rw [Equiv.apply_symm_apply]
    rfl
  refine ⟨Matrix.of fun a k => σ fun ρ => v (eT ρ) k (Fin.cast hr a), Matrix.ext fun a k => hσ.fin _, ?_⟩
  rw [hw, ← hL, hv]
  exact mul_ne_zero (Complex.exp_ne_zero _) (Finset.prod_ne_zero_iff.2 fun _ _ => hz)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem compare {σ : c.F →+* ℂ} (hA : l.A = 1) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {hr : T.rank = r}
    {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)} (hι : LatEmb T ι) {X X' : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {eT' : D.what₂.Tau ≃ X'.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
    {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {idx' : Fin g' ≃ X'.Ψ × Fin r}
    {e : Fin g ≃ Lt1 Dw} {e' : Fin g' ≃ Lt1 Dw} (hS : IsSet ψ θ S T hr X eT bas) (hS' : IsSet ψ θ S T hr X' eT' bas')
    (hM : Matched c σ X idx e) (hM' : Matched c σ X' idx' e') (hp : X'.p0 = X.p0) (hD : SelfD X X.Λ)
    (hD' : SelfD X' X'.Λ) {δ a' : GA D T} (hδ : δ ∈ GQ T) (hL : latW hr X.Λ = latG T (δ * a'))
    (hL' : latW hr X'.Λ = latG T a') {Z : Fam T} (hZ : IsONeg T X.p0 Z) {x : Frame X.Ψ r} {x' : Frame X'.Ψ r}
    (hx : x ∈ X.dom) (hx' : x' ∈ X'.dom) (ex : x = frOf hr eT (mvZ θ (δ * a') Z)) (ex' : x' = frOf hr eT' (mvZ θ a' Z)) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x X.Λ y) (A' : AnFib X' bas' idx' e' x' X'.Λ y')
      (th : (Fin g → ℂ) → ℂ) (th' : (Fin g' → ℂ) → ℂ), A.Reads 1 y.s th → A'.Reads 1 y'.s th' →
      ∀ mk mk' : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ X.Λ) → (∀ a, mk' a ∈ X'.Λ) →
      MarkAd hr l ι (δ * a') mk → MarkAd hr l ι a' mk' → A.Marked mk → A'.Marked mk' →
      ∃ lam : ℂ, (∀ a n, ∀ f ∈ sec Xo c a n, evR Xo c f y' = lam ^ n * evR Xo c f y) ∧
        ∀ w : WO S T, Ker.IsRealPt w → ∃ w' : WO S T, Ker.IsRealPt w' ∧
          Ker.gaussR X' bas' idx' x' (Ker.zR X' idx' x' (rePt θ hr eT' w')) *
              ∏ b, th' (Ker.zR X' idx' x' (rePt θ hr eT' w') b) =
            lam ^ S.rank * (Ker.gaussR X bas idx x (Ker.zR X idx x (rePt θ hr eT w)) *
              ∏ b, th (Ker.zR X idx x (rePt θ hr eT w) b)) ∧
          ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
            IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → om (1, δ * a') f w = om (1, a') f w' := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  intro y y' A A' th th' hth hth' mk mk' hmk hmk' hm hm' hAm hAm'
  have hX : SameSp X' X := sameSp_of_isSet hS hS' hp
  have hsy := symm_eq_of_isSet hS.2.2.2.2.2.2.1 hS'.2.2.2.2.2.2.1
  obtain ⟨ga, g1, g2, g3, g4, g5⟩ := GlobalTheory.OneMapRef.RatPt.rational_points D S T r g hr ψ θ X eT bas idx hS δ hδ
  obtain ⟨k1, k2⟩ := ((GlobalTheory.OneMapRef.markAd_laws D H Dw T r hr ι hι a' X'.Λ hL' l).2 mk' hmk' hm').2.2.2 δ ga g1
  have eL : mapL ga X'.Λ = X.Λ := latW_injective hr (k1.trans hL.symm)
  have eX : lact ga (castFr hX.psi x') = x := by
    have : castFr hX.psi x' = frOf hr eT (mvZ θ a' Z) := by
      rw [ex']
      funext τ a b
      simp only [castFr, frOf]
      rw [hsy τ.1 τ.2]
    rw [this, g3, ex, ((GlobalTheory.OneMapRef.oneg_frames D S T r g hr ψ θ X eT bas idx hS Z hZ).2.2.2.2 a').2.2.1 δ]
  have key := GlobalTheory.OneMapRef.anFib_move_renum D H Dw l Xo c σ r g g' X' X hX bas' idx' e' bas idx e hS'.2.2.2.2.2.2.2
    hS.2.2.2.2.2.2.2 hM' hM x' hx' X'.Λ hD' ga g2 y' A' th' hth'
  rw [eL, eX] at key
  obtain ⟨A₁, th₁, r1, r2, r3⟩ := key
  have hmem : ∀ a, mvMap ga mk' a ∈ X.Λ := fun a => eL ▸ ⟨mk' a, hmk' a, rfl⟩
  obtain ⟨m1, -, m3, -⟩ := (GlobalTheory.OneMapRef.markAd_laws D H Dw T r hr ι hι _ X.Λ hL l).2 _ hmem k2
  obtain ⟨lam, -, l2, l3⟩ := GlobalTheory.OneMapRef.exists_scalar_of_marked _ H Dw l Xo c r g X bas idx e x X.Λ hS.2.2.2.2.2.2.2 hx hD
    hA y y' A A₁ mk ((GlobalTheory.OneMapRef.markAd_laws D H Dw T r hr ι hι _ X.Λ hL l).2 _ hmk hm).1 hAm
    (marked_congr A₁ (r2 mk' hAm') (m3 l dvd_rfl le_rfl mk hmk hm)) th th₁ hth r1
  refine ⟨lam, l3, fun w hw => ?_⟩
  obtain ⟨w', hw', rfl⟩ := (g4 w).1 hw
  refine ⟨w', hw', ?_, fun χS χT om ho f hf => ?_⟩
  · rw [← r3 S.rank (rePt θ hr eT' w') (rePt θ hr eT (actO S T 1 δ w')), l2]
    · simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    · intro τ k
      rw [(g4 w').2]
      congr 1
      funext a
      change compAt θ (eT.symm ⟨τ.1, hX.psi ▸ τ.2⟩) w' (Fin.cast hr.symm a) k =
        compAt θ (eT'.symm τ) w' (Fin.cast hr.symm a) k
      rw [hsy τ.1 (hX.psi ▸ τ.2) τ.2]
  · have : ((1, δ * a') : GA D S × GA D T) = (1, δ) * (1, a') := by rw [Prod.mk_mul_mk, one_mul]
    rw [this, map_mul, Module.End.mul_apply]
    exact g5 χS χT om ho _ (ho.om_pres _ _ hf) w'

theorem rdU_eq {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) {x : Frame (U.X k).Ψ r}
    (hx : x ∈ (U.X k).dom) : rdU U f k x = @evR _ _ _ _ _ _ _ Xo c f ℂ _ σ.toAlgebra (ptC U k ⟨x, hx⟩) :=
  dif_pos hx

end GlobalTheory.OneMapRef.Equivar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointDeterminant_eq_normOneClass_of_level : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q) (y k : GL (Fin n) (AfE H.F H.E)) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), LevOk H SG SQ → IsPtOf (host_cmData R H) (y * k) (extTo SQ p) → k ∈ Formalism.L2.Herm.UstdAf (host_cmData R H) n → Formalism.L2.Herm.Carries k (stdLat H.E n) (stdLat H.E n) → (∀ P ∈ uSG SG SQ, Formalism.UG.bc (Formalism.UG.prV (E := H.E) (P.under (𝓞 H.F))) k = 1) → Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det y → detPt H SQ p = u1Dt H SQ x := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level | exact GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level | (intros; apply GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TuplePrimedSpaceClassesLevelAndComparisonStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuplePrimedSpaceClasses_level_and_comparison : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (KP : ClsPTied (D := I.rec7 l Z) u), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP I.mu0 KP.lev.Lb KP.lev.U KP.lev.chi (fun c => (KP.y c).1) KP.lat (fun c s => (KP.stabI c s).1) → ∃ K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q), K.lev.Lb = KP.lev.Lb ∧ (∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1) ∧ I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) ∧ (∀ v ∈ badG (I.rec7 l Z), K.lev.Uloc v = KP.lev.Uloc v) ∧ ∀ (κ : K.lev.U) (κ' : KP.lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → K.lev.chi κ = KP.lev.chi κ' := by
  first | exact @GlobalTheory.Mem.Col2.TC.tuplePrimedSpace_classes | exact GlobalTheory.Mem.Col2.TC.tuplePrimedSpace_classes | (intros; apply GlobalTheory.Mem.Col2.TC.tuplePrimedSpace_classes <;> assumption)
end

