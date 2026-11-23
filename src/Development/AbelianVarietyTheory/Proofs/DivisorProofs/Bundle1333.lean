module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDefiniteUnitaryAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsONBasis
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameLawsTheta

open GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant (realOf movS frameFn Fam)
open scoped ComplexOrder

theorem exists_isONBasis {n : ℕ} {G s : Matrix (Fin n) (Fin n) ℂ} (h : IsCartanInv G s) :
    ∃ (p : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), IsONBasis G s B p := by
  obtain ⟨p, q, B, B', hBB', hB'B, hG, hs⟩ := GlobalTheory.exists_basis_adapted_to_cartan_involution n G s h.1 h.2.1 h.2.2
  have hpq : p + q = n := by
    have h1 : Fintype.card (Fin n) ≤ Fintype.card (Fin p ⊕ Fin q) := by
      calc Fintype.card (Fin n) = (1 : Matrix (Fin n) (Fin n) ℂ).rank := (Matrix.rank_one).symm
        _ = (B * B').rank := by rw [hBB']
        _ ≤ B'.rank := Matrix.rank_mul_le_right _ _
        _ ≤ Fintype.card (Fin p ⊕ Fin q) := Matrix.rank_le_card_height _
    have h2 : Fintype.card (Fin p ⊕ Fin q) ≤ Fintype.card (Fin n) := by
      calc Fintype.card (Fin p ⊕ Fin q) = (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).rank := (Matrix.rank_one).symm
        _ = (B' * B).rank := by rw [hB'B]
        _ ≤ B.rank := Matrix.rank_mul_le_right _ _
        _ ≤ Fintype.card (Fin n) := Matrix.rank_le_card_height _
    simp only [Fintype.card_fin, Fintype.card_sum] at h1 h2
    omega
  subst hpq
  let e : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm
  have hd : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) =
      Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply] <;> split_ifs <;> simp
  have he : ∀ a : Fin (p + q), Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) (e a) =
      ((if (a : ℕ) < p then 1 else -1 : ℤ) : ℂ) := by
    intro a
    refine Fin.addCases (fun i => ?_) (fun j => ?_) a
    · simp [e, i.isLt]
    · simp [e]
  refine ⟨p, B.submatrix id e, fun a => if (a : ℕ) < p then 1 else -1, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : (a : ℕ) < p
    · exact Or.inl ⟨by simp [ha], ha⟩
    · exact Or.inr ⟨by simp [ha], by omega⟩
  · have : (B.submatrix id e)ᴴ * G * B.submatrix id e = (Bᴴ * G * B).submatrix e e := by
      rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
        Matrix.submatrix_id_id, Matrix.conjTranspose_submatrix]
    rw [this, hG, hd, Matrix.submatrix_diagonal_equiv]
    congr 1; funext a; rw [Function.comp_apply, he a]; split_ifs with hh <;> simp [hh]
  · have : s * B.submatrix id e = (s * B).submatrix id e := by
      rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
    rw [this, hs, hd]
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, id]
    erw [Matrix.mul_diagonal]
    rw [he j]
    split_ifs <;> simp

variable {D : D7}

end GlobalTheory.FrameLawsTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDefiniteUnitaryAdelicUnitaryGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_definiteUnitary_adelicUnitaryGroup : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    IsInfFam θ → V.SigOK → V.IsPosDef →
    ∃ (j : UA D.host.E V.rank ≃ₜ* GA D V) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
      cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 ∧
      (∀ x, x ∈ ratU D.host.E V.rank ↔ j x ∈ GQ V) ∧
      (∀ x, x ∈ finU (E := D.host.E) (n := V.rank) ↔ j x ∈ GfC V) ∧
      (∀ x, x ∈ infU D.host.E V.rank ↔ j x ∈ GinfC V) ∧
      (∃ A : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsUnit (A τ)) ∧
        ∀ τ x, infMat D.sp.cm.sig V.gram (θ τ) (j x) =
          A τ * (cEmb (tauE D τ) x : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (A τ)⁻¹) ∧
      (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  first | exact @GlobalTheory.DefTransfer.Glob.exists_iso | exact GlobalTheory.DefTransfer.Glob.exists_iso | (intros; apply GlobalTheory.DefTransfer.Glob.exists_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSectionsZeroSchemeRegularSequenceLineB
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.RegSeqGlue

open GlobalTheory.Twist

variable {Y : Scheme.{0}} {L : LB Y}

def LocSpan (F : Y.Modules) {d : ℕ} (t : Fin d → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (x : Γ(twistZ F L m, O)) : Prop :=
  ∀ y ∈ O, ∃ (V : Y.Opens) (hV : V ≤ O), y ∈ V ∧ ∃ c : Fin d → Γ(twistZ F L l, V),
    (twistZ F L m).presheaf.map (homOfLE hV).op x = ∑ i, (mulSecOfEq F (zofSec (t i)) h).app V (c i)

theorem res_res (G : Y.Modules) {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(G, U)) :
    G.presheaf.map (homOfLE h₁).op (G.presheaf.map (homOfLE h₂).op x) =
      G.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem eq_zero_of_locSpan (F : Y.Modules) (t : Fin 0 → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (x : Γ(twistZ F L m, O)) (hx : LocSpan F t h x) : x = 0 :=
  section_eq_zero_of_germ x fun y hy => by
    obtain ⟨V, hV, hyV, c, e⟩ := hx y hy
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hV) y hyV, e, Finset.univ_eq_empty, Finset.sum_empty, map_zero]

variable (hL : L.IsLB)

theorem π_mul (F : Y.Modules) (s a : L.Sec) {l m : ℤ} (h : l + 1 = m) (V : Y.Opens) (u : Γ(twistZ F L l, V)) :
    (Twist.map (lbZPow L m) (cutπ F hL s)).app V ((mulSecOfEq F (zofSec a) h).app V u) =
      (mulSecOfEq (cut F hL s) (zofSec a) h).app V ((Twist.map (lbZPow L l) (cutπ F hL s)).app V u) := by
  rw [app_app, app_app, mulSecOfEq_naturality]

theorem map_locSpan (F : Y.Modules) {d : ℕ} (t : Fin (d + 1) → L.Sec) [Mono (cutHom F hL (t 0))] {l m : ℤ}
    (h : l + 1 = m) {O : Y.Opens} {x : Γ(twistZ F L m, O)} (hx : LocSpan F t h x) :
    LocSpan (cut F hL (t 0)) (fun i => t i.succ) h ((Twist.map (lbZPow L m) (cutπ F hL (t 0))).app O x) :=
  fun y hy => by
    obtain ⟨V, hV, hyV, c, e⟩ := hx y hy
    refine ⟨V, hV, hyV, fun i => (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app V (c i.succ), ?_⟩
    have := (RegSeqKer.shortExact_twistComplex hL F (t 0) h).mono_f
    have hex : Function.Exact ((mulSecOfEq F (zofSec (t 0)) h).app V)
        ((Twist.map (lbZPow L m) (cutπ F hL (t 0))).app V) :=
      exact_app_of_exact_of_mono (RegSeqKer.shortExact_twistComplex hL F (t 0) h).exact V
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← app_res, e, Fin.sum_univ_succ, map_add (f := _), hex.apply_apply_eq_zero, zero_add, map_sum]
    exact Finset.sum_congr rfl fun i _ => π_mul hL F _ _ h V _

theorem exists_glue (d : ℕ) : ∀ (t : Fin d → L.Sec) (F : Y.Modules) [F.IsQuasicoherent] (j₀ l m : ℤ)
    (h : l + 1 = m), RegSeq hL F (List.ofFn t) → VanishFrom L F j₀ → j₀ + d ≤ m →
    ∀ (W : Y → Y.Opens) (b : ∀ y, Γ(twistZ F L m, W y)), (∀ y, y ∈ W y) →
    (∀ y z, LocSpan F t h ((twistZ F L m).presheaf.map (homOfLE (inf_le_left : W y ⊓ W z ≤ W y)).op (b y) -
      (twistZ F L m).presheaf.map (homOfLE (inf_le_right : W y ⊓ W z ≤ W z)).op (b z))) →
    ∃ σ : Γ(twistZ F L m, ⊤), ∀ y, LocSpan F t h ((twistZ F L m).presheaf.map (homOfLE le_top).op σ - b y) := by
  induction d with
  | zero =>
    intro t F _ j₀ l m h _ _ _ W b hW hb
    have hc : ∀ y z, (twistZ F L m).presheaf.map (homOfLE (inf_le_left : W y ⊓ W z ≤ W y)).op (b y) =
        (twistZ F L m).presheaf.map (homOfLE (inf_le_right : W y ⊓ W z ≤ W z)).op (b z) := fun y z =>
      sub_eq_zero.1 (eq_zero_of_locSpan F t h _ (hb y z))
    obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨(twistZ F L m).presheaf, (twistZ F L m).isSheaf⟩ W ⊤
      (fun y => homOfLE le_top) (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) b (fun y z => hc y z)
    refine ⟨σ, fun y z hz => ⟨W y, le_rfl, hz, fun i => i.elim0, ?_⟩⟩
    rw [hσ y, sub_self, map_zero, Finset.univ_eq_empty, Finset.sum_empty]
  | succ d ih =>
    intro t F _ j₀ l m h hr hv hj W b hW hb
    rw [List.ofFn_succ, regSeq_cons] at hr
    obtain ⟨hm0, hr⟩ := hr
    have hS := RegSeqKer.shortExact_twistComplex hL F (t 0) h
    have := hS.mono_f
    have hex : ∀ V : Y.Opens, Function.Exact ((mulSecOfEq F (zofSec (t 0)) h).app V)
        ((Twist.map (lbZPow L m) (cutπ F hL (t 0))).app V) := fun V =>
      exact_app_of_exact_of_mono hS.exact V
    obtain ⟨σ', hσ'⟩ := ih (fun i => t i.succ) (cut F hL (t 0)) (j₀ + 1) l m h hr
      (RegSeqKer.vanishFrom_cut hL F (t 0) hv) (by push_cast at hj; omega) W
      (fun y => (Twist.map (lbZPow L m) (cutπ F hL (t 0))).app (W y) (b y)) hW fun y z => by
        have := map_locSpan hL F t h (hb y z)
        rwa [map_sub, app_res, app_res] at this
    obtain ⟨σ, hσ⟩ := cohOn.app_surjective hS ⊤ (hv l (by push_cast at hj; omega) 1 one_pos) σ'
    change (Twist.map (lbZPow L m) (cutπ F hL (t 0))).app ⊤ σ = σ' at hσ
    have hEpi : Epi (Twist.map (lbZPow L l) (cutπ F hL (t 0))) :=
      (RegSeqKer.shortExact_twistComplex hL F (t 0) (l := l - 1) (m := l) (by omega)).epi_g
    have := isQuasicoherent_twist (F := F) (isLB_lbZPow hL l)
    have := isQuasicoherent_twist (F := cut F hL (t 0)) (isLB_lbZPow hL l)
    refine ⟨σ, fun y z hz => ?_⟩
    obtain ⟨V, hV, hzV, c', e⟩ := hσ' y z hz
    obtain ⟨A, hzA, hAV⟩ := exists_affine hzV
    have hlift : ∀ i, ∃ u : Γ(twistZ F L l, A.1), (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app A.1 u =
        (twistZ (cut F hL (t 0)) L l).presheaf.map (homOfLE hAV).op (c' i) := fun i =>
      surjective_app_of_epi _ A.2 _
    choose u hu using hlift
    obtain ⟨v, hv'⟩ := (hex A.1 ((twistZ F L m).presheaf.map (homOfLE (hAV.trans hV)).op
        ((twistZ F L m).presheaf.map (homOfLE le_top).op σ - b y) -
        ∑ i, (mulSecOfEq F (zofSec (t i.succ)) h).app A.1 (u i))).1 (by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, sub_eq_zero]
      erw [app_res, map_sub, app_res, hσ]
      rw [← res_res _ hAV hV]
      erw [e]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [π_mul, hu]
      exact (app_res _ _ _).symm)
    refine ⟨A.1, hAV.trans hV, hzA, Fin.cons v u, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hv', sub_add_cancel]

end GlobalTheory.HSCore.RegSeqGlue

namespace GlobalTheory.HSCore.RegSeqGlue

open GlobalTheory.Twist GlobalTheory.HSKerRes

variable {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) {M L : LB Y} (hM : M.IsLB) (hL : L.IsLB)


include hM hL in
theorem toH0_res {n : ℤ} {O O' : Y.Opens} (h : O' ≤ O) (s : Γ(twistZ (LB.toMod M) L n, O)) :
    toH0 p ((twistZ (LB.toMod M) L n).presheaf.map (homOfLE h).op s) = H0.restr h (toH0 p s) :=
  tw_ext hM hL fun i j y hy hi hj => by
    rw [H0.germ_restr, germ_of_global_section p _ i j y _ hi hj, germ_of_global_section p _ i j y _ hi hj]
    erw [Twist.zcoord_resM]
    rw [HSKerRes.coord_resM, ger_resG]


include hM in
theorem vanishesTo_mulSec {d : ℕ} (t : Fin d → L.Sec) (a : Fin d) {n l : ℤ} (h : n + 1 = l) {O : Y.Opens}
    (f : Vanishing.H0 p (tw M L n) O) : VanishesTo (cutIdeal hL t) 1 (mulSec hM hL (t a) h f) :=
  vanishesTo_of_exists fun y _ hy => by
    obtain ⟨i, hi⟩ := exists_chart hM y
    obtain ⟨j, hj⟩ := exists_chart hL y
    refine ⟨twIdx l i j, mem_tw_U.2 ⟨hi, hj⟩, ?_⟩
    rw [germ_mulSec _ _ _ _ _ _ _ _ _ hi hj, pow_one, stalkId_cutIdeal hL t j y hj]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, rfl⟩)


include hM in
theorem vanishesTo_of_locSpan {d : ℕ} (t : Fin d → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (x : Γ(twistZ (LB.toMod M) L m, O)) (hx : LocSpan (LB.toMod M) t h x) :
    VanishesTo (cutIdeal hL t) 1 (toH0 p x) := fun y hs hy i hi => by
  obtain ⟨V, hV, hyV, c, e⟩ := hx y hy
  have hv : VanishesTo (cutIdeal hL t) 1 (H0.restr hV (toH0 p x)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← toH0_res p hM hL, e, map_sum]
    show _ ∈ filTop p _ V (cutIdeal hL t) 1
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [mem_filTop, global_section_mul p hM hL (t a) h]
    exact vanishesTo_mulSec p hM hL t a h _
  have := hv y hs hyV i hi
  rwa [H0.germ_restr] at this


include hM in
theorem locSpan_of_vanishesTo {d : ℕ} (t : Fin d → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (s : Γ(twistZ (LB.toMod M) L m, O)) (hs : VanishesTo (cutIdeal hL t) 1 (toH0 p s)) :
    LocSpan (LB.toMod M) t h s := fun y hy => by
  obtain ⟨i, hi⟩ := exists_chart hM y
  obtain ⟨j, hj⟩ := exists_chart hL y
  obtain ⟨V, hV, e⟩ := exists_affine (memInf (memInf hy hi) hj)
  have hVO : V.1 ≤ O := e.trans (inf_le_left.trans inf_le_left)
  have hVi : V.1 ≤ M.U i := e.trans (inf_le_left.trans inf_le_right)
  have hVj : V.1 ≤ L.U j := e.trans inf_le_right
  have h₁ : V.1 ≤ O ⊓ (tw M L m).U (twIdx m i j) := fun _ hz => ⟨hVO hz, mem_tw_U.2 ⟨hVi hz, hVj hz⟩⟩
  have h₂ := vanishesTo_iff_affine.1 hs V _ h₁
  rw [pow_one, ideal_cutIdeal hL t V j hVj, restricted_section_chart_coords p s i j h₁ (le_inf (le_inf hVO hVj) hVi)] at h₂
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h₂
  refine ⟨V.1, hVO, hV, fun a => (Twist.zchartEquiv hL l j hVj).symm ((LB.chartEquiv hM i hVi).symm (c a)), ?_⟩
  refine (Twist.zchartEquiv hL m j hVj).injective ((LB.chartEquiv hM i hVi).injective ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Twist.zchartEquiv_mulSecOfEq_app, map_smul, LinearEquiv.apply_symm_apply, Twist.zfun_zofSec,
    smul_eq_mul]
  rw [LB.chartEquiv_apply, Twist.zchartEquiv_apply]
  refine Eq.trans ?_ (hc.symm.trans (Finset.sum_congr rfl fun a _ => mul_comm _ _))
  rw [HSKerRes.coord_resM]
  erw [Twist.zcoord_resM]
  rw [HSKerRes.coord_resM, LB.resG_resG, LB.resG_resG]

end GlobalTheory.HSCore.RegSeqGlue

theorem GlobalTheory.HSCore.exists_glue_mod_regSeq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (p : Y ⟶ Sp k) (M L : LB Y), M.IsLB → ∀ (hL : L.IsLB) (d : ℕ) (t : Fin d → L.Sec) (l : ℤ), RegSeq hL (GlobalTheory.LB.toMod M) (List.ofFn t) → VanishFrom L (GlobalTheory.LB.toMod M) 0 → (d : ℤ) ≤ l → ∀ (W : Y → Y.Opens) (b : ∀ y, Vanishing.H0 p (tw M L l) (W y)), (∀ y, y ∈ W y) → (∀ y z, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr inf_le_left (b y) - Vanishing.H0.restr inf_le_right (b z) : Vanishing.H0 p (tw M L l) (W y ⊓ W z))) → ∃ σ : Vanishing.H0 p (tw M L l) ⊤, ∀ y, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr le_top σ - b y) := by
  intro k _ Y _ _ p M L hM hL d t l hreg hvan hd W b hW hb
  have hl : l - 1 + 1 = l := by omega
  have := (VB.isVB_toMod hM).isFiniteQC
  have hs : ∀ y, ∃ β : Γ(twistZ (LB.toMod M) L l, W y), HSKerRes.toH0 p β = b y := fun y =>
    HSKerRes.surjective_ofTwist hM (Twist.isLB_lbZPow hL _) (b y)
  choose β hβ using hs
  obtain ⟨σ, hσ⟩ := RegSeqGlue.exists_glue hL d t (LB.toMod M) 0 (l - 1) l hl hreg hvan (by omega) W β hW
    fun y z => RegSeqGlue.locSpan_of_vanishesTo p hM hL t hl _ (by
      rw [map_sub, RegSeqGlue.toH0_res p hM hL, RegSeqGlue.toH0_res p hM hL, hβ, hβ]
      exact hb y z)
  refine ⟨HSKerRes.toH0 p σ, fun y => ?_⟩
  have := RegSeqGlue.vanishesTo_of_locSpan p hM hL t hl _ (hσ y)
  rwa [map_sub, RegSeqGlue.toH0_res p hM hL, hβ] at this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyNormalOpenArithmeticVariety
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.NormalOpen

theorem exists_mul_isInteger (A K : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Module.Finite A (integralClosure A K)] :
    ∃ f : A, f ≠ 0 ∧ ∀ y : K, IsIntegral A y → ∃ a : A, algebraMap A K a = f • y := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := integralClosure A K)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (s.image fun z : integralClosure A K => (z : K))
  refine ⟨b, nonZeroDivisors.ne_zero b.2, fun y hy => ?_⟩
  have key : ∀ z ∈ Submodule.span A (s : Set (integralClosure A K)),
      ∃ a : A, algebraMap A K a = (b : A) • (z : K) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hb _ (Finset.mem_image_of_mem _ hx)
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨a + c, by rw [map_add (f := _), ha, hc, Subalgebra.coe_add, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      rw [map_mul, ha, Subalgebra.coe_smul, smul_comm, ← Algebra.smul_def]
  exact key ⟨y, hy⟩ (hs ▸ Submodule.mem_top)

theorem exists_isIntegrallyClosed_away (A : Type*) [CommRing A] [IsDomain A]
    [Module.Finite A (integralClosure A (FractionRing A))] :
    ∃ f : A, f ≠ 0 ∧ IsIntegrallyClosed (Localization.Away f) := by
  let K := FractionRing A
  obtain ⟨f, hf, h⟩ := exists_mul_isInteger A K
  refine ⟨f, hf, ?_⟩
  let B := Localization.Away f
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hg : ∀ y : Submonoid.powers f, IsUnit (algebraMap A K y) := fun y =>
    IsLocalization.map_units K (⟨y, hle y.2⟩ : nonZeroDivisors A)
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _ hle
  letI : Algebra B K := (IsLocalization.lift (S := B) hg).toAlgebra
  have : IsScalarTower A B K := .of_algebraMap_eq fun a => (IsLocalization.lift_eq hg a).symm
  have : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) B K
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers f)
    (Rₘ := B) x hx
  obtain ⟨a, ha⟩ := h _ hm
  let t : Submonoid.powers f := ⟨f, Submonoid.mem_powers f⟩ * m
  refine ⟨IsLocalization.mk' B a t, ?_⟩
  have e := congrArg (algebraMap B K) (IsLocalization.mk'_spec B a t)
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ha] at e
  refine (hg t).mul_right_cancel ?_
  rw [e, mul_comm, ← Algebra.smul_def, Submonoid.smul_def, smul_smul]
  rfl

theorem exists_normal_opens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∃ Ω : X.Opens, (Ω : Set X).Nonempty ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Ω.toScheme := by
  intro k _ X p D h
  have := h.isIntegral
  have := h.finite
  obtain ⟨A, _, _, i, _, a, -, hi⟩ := exists_affine_chart_over p (genericPoint X)
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
  obtain ⟨_, hft, -⟩ := RegGenSmooth.chart_props h i hi
  have : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans (S := k) inferInstance hft
  have := finite_integralClosure_of_essFiniteType_int A
  obtain ⟨f, hf, hc⟩ := exists_isIntegrallyClosed_away A
  let B := Localization.Away f
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsOpenImmersion (spMap (algebraMap A B)) := IsOpenImmersion.of_isLocalization f
  let j : Sp B ⟶ X := spMap (algebraMap A B) ≫ i
  have hB : GlobalTheory.IsNormalScheme (Sp B) := GlobalTheory.IsNormalScheme.spec (.of B)
  have : GlobalTheory.IsNormalScheme j.opensRange.toScheme := .of_isIso j.isoOpensRange.hom
  refine ⟨j.opensRange, ?_, GlobalTheory.IsNormalScheme.pred _⟩
  exact ⟨j (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B), _, rfl⟩

end GlobalTheory.NormalOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapCancel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField TensorProduct
open GlobalTheory.UPel.HT GlobalTheory.IwLevel GlobalTheory.UPel.HT.MapComp

namespace GlobalTheory.IwLevel

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_objMap_cancel {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : ObjMap o₁ o₃ (f ≫ g)) (m₂ : ObjMap o₂ o₃ g) :
    ∃ m' : ObjMap o₁ o₂ f, m'.φ ≫ m₂.φ = m.φ := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := isSquare_unique m.sq (hφ ▸ isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }, hφ⟩

end GlobalTheory.IwLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HcfjHolds
section
namespace GlobalTheory.Laid

theorem hcfj_holds : GlobalTheory.Published.HilbertClassFieldJ := GlobalTheory.CompanionTheory.Hypotheses₂.hilbertClassFieldJ

end GlobalTheory.Laid
end

