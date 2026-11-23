module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationality
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0412
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexValueDetShiftMulRatSpan
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerValRat

theorem lamTG_add_sSharp {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : Fin (D.R.N i)) :
    (lamTG M i τ).w r + (D.chTw u μ).sSharp i τ = (nuT D u i τ r : ℤ) := by
  obtain ⟨a, ha⟩ := D.R.t_odd
  have hc : ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) = (i : ℝ) * ((a : ℝ) + 1) := by
    rw [ha, show i * (2 * a + 1 + 1) = 2 * (i * (a + 1)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    push_cast; ring
  have ht : (D.R.t : ℝ) = 2 * a + 1 := by rw [ha]; push_cast; ring
  have h1 := congrArg (Rat.cast : ℚ → ℝ) (M.lam_eq i hi.le τ r)
  have h2 := congrArg (Rat.cast : ℚ → ℝ) ((D.chTw u μ).sSharp_eq i hi τ)
  have h3 := GlobalTheory.PdvKm.nuT_real u i hi τ r
  have he := D.hcW_e u τ
  suffices key : (((lamTG M i τ).w r : ℤ) : ℝ) + (((D.chTw u μ).sSharp i τ : ℤ) : ℝ) = ((nuT D u i τ r : ℕ) : ℝ) by
    exact_mod_cast key
  rw [h3]
  have e0 : (lamTG M i τ).w r = (M.lam i τ).w r - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ) := rfl
  have hl : (((lamTG M i τ).w r : ℤ) : ℝ) = ((((M.lam i τ).w r : ℤ) : ℚ) : ℝ) - (i : ℝ) * ((a : ℝ) + 1) := by
    rw [e0, Int.cast_sub, Int.cast_natCast, hc, Rat.cast_intCast]
  have hs : (((D.chTw u μ).sSharp i τ : ℤ) : ℝ) = ((((D.chTw u μ).sSharp i τ : ℤ) : ℚ) : ℝ) := by rw [Rat.cast_intCast]
  rw [hl, hs, h1, h2]
  have hw : DV.wSz D (i + 1) τ = (((D.hcW u τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
    unfold DV.wSz
    rw [dite_eq_left ⟨by omega, by omega⟩, he]
    rfl
  unfold DV.nuRow
  rw [hw]
  unfold DV.srcPar sExp' Ranks.N
  by_cases hk : r.1 < D.R.k
  · rw [dite_eq_left hk, dite_eq_left hk]
    unfold hcToWeightQ rhoVec
    push_cast
    rw [ht]
    ring
  · rw [dite_eq_right hk, dite_eq_right hk]
    have hr := r.2
    unfold Ranks.N at hr
    have hb : (r.1 - D.R.k) / (D.R.t + 1) < i := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      exact Nat.sub_lt_left_of_lt_add (by omega) hr
    have hbm : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by omega
    rw [dite_eq_left hbm]
    have hdm := Nat.div_add_mod (r.1 - D.R.k) (D.R.t + 1)
    have hr' : (r.1 : ℝ) = D.R.k + (D.R.t + 1) * (((r.1 - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) + (((r.1 - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      have : r.1 = D.R.k + ((D.R.t + 1) * ((r.1 - D.R.k) / (D.R.t + 1)) + (r.1 - D.R.k) % (D.R.t + 1)) := by omega
      conv_lhs => rw [this]
      push_cast; ring
    unfold wG
    push_cast
    rw [hr', ht]
    ring

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

open GlobalTheory.PdvKm in
theorem detShift_lamTG {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    (lamTG M i τ).detShift = (nuT D u i τ (lastI D i) : ℤ) - (D.chTw u μ).sSharp i τ := by
  have h := lamTG_add_sSharp M μ i hi τ (lastI D i)
  unfold DomWeight.detShift
  rw [dite_eq_left (N_pos D i)]
  show (lamTG M i τ).w (lastI D i) = _
  omega

open GlobalTheory.PdvKm in
theorem natW_lamTG {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : Fin (D.R.N i)) :
    (M.lam i τ).natW r = nuT D u i τ r - nuT D u i τ (lastI D i) := by
  have h0 : (M.lam i τ).natW r = (lamTG M i τ).natW r := by
    show _ = (Formalism.L2.Forms.shW (M.lam i τ) _).natW r
    rw [Formalism.L2.Forms.natW_shW]
  rw [h0]
  have h1 := lamTG_add_sSharp M D.what₂.mu0 i hi τ r
  have h2 := detShift_lamTG M D.what₂.mu0 i hi τ
  have hle : nuT D u i τ (lastI D i) ≤ nuT D u i τ r :=
    antitone_kernelChain_nuT D u i τ hi (show r ≤ lastI D i by rw [Fin.le_def]; simp only [lastI]; omega)
  unfold DomWeight.natW
  rw [h2]
  omega

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

open GlobalTheory.PdvKm in
theorem evC_ratSpan_gen {D : D7} (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup)
    {A : ColumnsAtT D.R (D.chTw u μ)} {P : PeriodMap D.R (D.chTw u μ)}
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) (D.chTw u μ) A P)
    (i : ℕ) (hi : i < D.R.m) (eY : (D.chTw u μ).Y i ≃ Fr D i hi.le)
    (hfrm : ∀ y, (O u μ).frm i y = (eY y).1) (v : ValQ O u μ i) :
    ∃ Q ∈ Formalism.L2.Forms.RatSpan D (M.lam i), ∀ z, evC O u μ i v z =
      fnOf (gramC (gramN D i hi.le) (embT D)) (shiftOf (lamTG M i)) 1 Q (eY z) := by
  have hne : ∀ (z : (D.chTw u μ).Y i) τ, ((eY z).1 τ).det ≠ 0 := fun z τ => by
    rw [← hfrm z, ← (O u μ).frm_de i hi.le z τ]; exact (D.chTw u μ).de_ne i z τ
  have hev : ∀ z, evC O u μ i v z = (∏ τ, (((eY z).1 τ).det) ^ (-(twB D u μ i τ))) *
      MvPolynomial.eval₂ D.what₂.embLL (fun k => (eY z).1 k.1 k.2.1 k.2.2)
        (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL) := by
    intro z
    rw [evC_sec]
    show (∏ τ, ((D.chTw u μ).de i z τ) ^ (-(twB D u μ i τ))) *
      GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) ((O u μ).frm i z) = _
    simp only [(O u μ).frm_de i hi.le z, hfrm z, evFr_map]
  have hfn : ∀ (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ) z,
      fnOf (gramC (gramN D i hi.le) (embT D)) (shiftOf (lamTG M i)) 1 Q (eY z) =
        (∏ τ, ((eY z).1 τ).det ^ (lamTG M i τ).detShift) * MvPolynomial.eval (fun x => (eY z).1 x.1 x.2.1 x.2.2) Q := by
    intro Q z
    show (∏ τ, ((1 : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) τ * (eY z).1 τ).det ^ _) *
      MvPolynomial.eval (fun x => ((1 : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) x.1 * (eY z).1 x.1) x.2.1 x.2.2) Q = _
    simp only [Pi.one_apply, one_mul]
    rfl

  haveI hLL : Infinite D.what₂.LL := Infinite.of_injective (fun n : ℕ => (n : D.what₂.LL)) (fun a b h => by
    have := congrArg D.what₂.embLL h; simp only [map_natCast] at this; exact_mod_cast this)
  have hmem : (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL) ∈ polV D u i := (secC O u μ i v).2
  rcases i with _ | j
  · have h0 : 0 < D.R.m := hi
    have hk : ∀ τ r, nuT D u 0 τ (lastI D 0) ≤ nuT D u 0 τ r := fun τ r =>
      antitone_kernelChain_nuT D u 0 τ h0 (show r ≤ lastI D 0 by rw [Fin.le_def]; simp only [lastI]; omega)
    obtain ⟨P0, hP0, hQe⟩ := frameWeightPolyDivByDet_proof D.what₂.LL D.what₂.Tau (D.R.N 0) (nuT D u 0) (fun τ => nuT D u 0 τ (lastI D 0)) hk _ hmem
    refine ⟨MvPolynomial.map D.what₂.embLL P0, GlobalTheory.LevelHecke.map_mem_ratSpan (M.lam 0) ?_, fun z => ?_⟩
    · rw [VV_eq_WtPol]
      have e : (fun τ r => (M.lam 0 τ).natW r) = fun τ r => nuT D u 0 τ r - nuT D u 0 τ (lastI D 0) :=
        funext fun τ => funext fun r => natW_lamTG M 0 h0 τ r
      rw [e]; exact hP0
    · have hd : ∀ τ, MvPolynomial.eval₂ D.what₂.embLL (fun k : GL3Theta.FrV D (D.R.N 0) => (eY z).1 k.1 k.2.1 k.2.2)
          (frDet D.what₂.LL (D.R.N 0) τ) = ((eY z).1 τ).det := by
        intro τ
        rw [← MvPolynomial.eval_map, Formalism.L2.Ker.map_frDet, Formalism.L2.Ker.eval_frDet]
        rfl
      rw [hev, hfn, hQe, MvPolynomial.eval_map, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod]
      simp only [MvPolynomial.eval₂_pow, hd]
      have hs : ∀ τ, (lamTG M 0 τ).detShift = ((nuT D u 0 τ (lastI D 0) : ℕ) : ℤ) - twB D u μ 0 τ :=
        fun τ => detShift_lamTG M μ 0 h0 τ
      simp only [hs]
      rw [prod_zpow_split _ (hne z) _ (fun τ => nuT D u 0 τ (lastI D 0))]
      ring
  · have hj : j < D.R.m := by omega
    refine ⟨MvPolynomial.map D.what₂.embLL (secC O u μ (j + 1) v : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) D.what₂.LL),
      GlobalTheory.LevelHecke.map_mem_ratSpan (M.lam (j + 1)) ?_, fun z => ?_⟩
    · rw [VV_eq_WtPol]
      have e : (fun τ r => (M.lam (j + 1) τ).natW r) = extNu (D.R.N (j + 1)) (nuT D u j) := by
        funext τ r
        rw [natW_lamTG M (j + 1) hi τ r, ← natW_succ (antitone_kernelChain_nuT D) u j hj τ r]
        have h1 := clause1 (antitone_kernelChain_nuT D) u (j + 1) hi τ r
        have h2 : nn D u (j + 1) τ = nuT D u (j + 1) τ (lastI D (j + 1)) := by unfold nn; rw [if_pos hi]
        omega
      rw [e]; exact hmem
    · rw [hev, hfn, MvPolynomial.eval_map]
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      congr 1
      rw [detShift_lamTG M μ (j + 1) hi τ]
      have h1 := last_real u μ j hi τ
      show -((D.chTw u μ).sDiv j τ) = _
      have h2 : ((nuT D u (j + 1) τ (lastI D (j + 1)) : ℕ) : ℤ) = (D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ := by
        exact_mod_cast h1
      omega

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

theorem evC_ratSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ v : ValQ O u μ i, ∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, evC O u μ i v z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z) := by
  intro B X I hOk hPins l Z Y O hQ hS u μ i hi eY hId v
  exact evC_ratSpan_gen O u μ (I.fm l u μ) i hi eY (fun y => (hS.frm u μ i y).trans (hId y).symm) v

end GlobalTheory.KerValRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstOfConstOnDictLat
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem const_of_const_on_dictLat : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 → gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)) → IsUnf U → (∀ k, ModelW V hr (U.X k)) → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictLat U V hr dict io e F ik φ th x₀ → ∀ f ∈ sec Xo c 0 0, ∀ c0 : ℂ, (∀ h, rdU U f (dict h).1 (dict h).2 = c0) → ∀ y : FrPt Xo c (CAt σ), toC (evR Xo c f y) = c0 := by
  intro D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hι hpq hA hσ hx hU hW hth hD f hf c0 hc y
  subst hr
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀ := fun k τ hτ => by
    rw [(hW k).1, (hU.2.1 k).1]
    exact hx τ (((hU.2.1 k).2 τ).1 hτ)
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, -⟩ := _root_.GlobalTheory.Member.Arch.archM_spec D V θ hθ
  have hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom := by
    intro h
    obtain ⟨γ, -, -, -, hfr⟩ := hD.2 h
    refine ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank (U.X _).p0
      (U.X _).Ψ (U.X _).Gm (U.X _).Gm_herm).2.1 _ fun τ => ?_).1
    rw [hfr τ, GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ τ) (hθ τ.1), ← hx₀ _ τ.1 τ.2, hG]
    have hu := (hAr τ.1).2.2.2.2 (γ * h)
    have hg : ∀ x : Matrix (Fin V.rank) (Fin V.rank) ℂ,
        gram τ.1 (-V.gramᵀ) x = xᵀ * (-V.gramᵀ).map τ.1 * x.map (starRingEnd ℂ) := fun x => by
      ext a b
      simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
        Finset.sum_mul]
      exact Finset.sum_comm
    change gram τ.1 _ (archM V (θ τ.1) (γ * h) * x₀ τ.1) = _
    rw [hg, hg, Matrix.transpose_mul, Matrix.map_mul]
    conv_rhs => rw [← hu]
    simp only [Matrix.mul_assoc]
  obtain ⟨h, hh⟩ := GlobalTheory.TwistTie.exists_dict_over V U dict io e F ik φ th x₀ hσ hA hpq hU hW hD hι hth hx₀ hdom y
  rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hf hh, ← hc h]
  exact (dif_pos (hdom h) : rdU U f (dict h).1 (dict h).2 = _).symm

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedRowLatticesFlagLevelRightTranslation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco

theorem deco_tie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q),
    ∃ u : ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp,
      (∀ h : Bridge.Gf X.toD7.sp.X', RowAd.decoAd X I t (h * (q : Bridge.Gf X.toD7.sp.X')) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)),
          (u : Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
            (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
              (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)))))⁻¹) •
          RowAd.decoAd X I t h) ∧
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr u : X.B.fields.Kˣ) : X.B.fields.K) =
        (((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch q : ℂˣ) : ℂ) := by
  intro X px I hX U L eG hI hV hL hG t q
  have hz := unitaryFiniteAdelicPointAsMatrix_mem_flagIwahori X I hI L hL t q
  have hu := GlobalTheory.T.inv_reduction_mul_flagTranslation_mem_rowLevelGroup X px I U L eG hI hL hG t q hz
  refine ⟨⟨_, hu⟩, fun h => ?_, GlobalTheory.T.rowLevelCharacter_translation_eq_flagCharacter X px I U L eG hI hV hL hG t q hz hu⟩
  refine (decoAd_mul X I hI t h _ hz).trans ?_
  refine congrArg (fun a : Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) =>
    ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)), a) • RowAd.decoAd X I t h) ?_
  exact (mul_inv_cancel_right _ _).symm

end GlobalTheory.Mem.R3.RowDeco
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdStdBot
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

structure StdKerTie {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop where
  X_eq : t.X = B.fields
  seam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
  Pr : HEq t.Pr (B.primes X)
  Ch : HEq t.Ch I.Ch
  sel : HEq t.sel I.sel
  S : t.S = I.S
  word : HEq t.word fun u : B.Word => u
  tup : HEq t.tup I.tup
  cst : HEq t.cst I.cst
  idx : HEq t.idx I.idx
  m2 : t.m2 = B.R.m - 2
  glob : HEq t.glob I.glob
  amb : HEq t.amb (I.J.amb B t.χ)
  δ : t.δ = I.J.δ
  O : I.StdO l Z Y.Qp t.O

namespace StdKerEmpty

end StdKerEmpty

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeLocalBasisIffUnimodularCompanion
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.DualOffLevel

theorem mem_divs_of {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A}
    (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact (hf.mem_toFinset.1 h)
  · simp at h

theorem isLocBasis_dual_iff_N : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (u : B.Word) (a : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u a w → ∀ (i : ℕ) (hi : i ≤ B.R.m) (c : (I.stp u a i).Cl) (Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c))) Bm ↔ Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u a i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm := by
  intro B X I hOk hPins l Z Y u a w hw i hi c Bm
  classical
  have hpP : ((I.rec7 l Z).what₂.places.resChar w).Prime := (I.rec7 l Z).what₂.places.resChar_prime w
  have hTP : (B.T u).Prime := l.pr.T_prime u
  have hpT : ¬ (I.rec7 l Z).what₂.places.resChar w ∣ B.T u := fun h => hw.1 ((Nat.prime_dvd_prime_iff_eq hpP hTP).1 h)
  obtain ⟨hG, -, hc⟩ := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi
  have hL := (hc u a).1 c
  have hS : dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)
      (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) =
      (((I.stp u a i).rep c).1.1.deco.1.Lsh : Set (Sp B.fields.E (B.R.N i))) := by
    rw [hG, hL]
    exact GlobalTheory.Mem.Col2.ValTie.dualSet_std (E := B.fields.E) _ (fun _ => rfl) _
  rw [hS]
  set d := ((I.stp u a i).rep c).1.1.deco with hd
  have hTP' : ∀ P : (B.primes X).vT u, (((B.T u : ℕ) : 𝓞 B.fields.E)) ∈ (P : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal := by
    intro P
    have hpi := mem_divs_of P.2
    rw [← l.pr.piT_norm u]
    exact Ideal.mul_mem_right _ _ hpi
  have hLN : ∀ x ∈ d.1.Lsh, ((B.T u : ℕ) : B.fields.E) • x ∈ d.1.N := by
    intro x hx
    have := d.2.smul_Lsh_mem_N (a := ((B.T u : ℕ) : 𝓞 B.fields.E)) (fun P => by rw [map_natCast]; exact hTP' P) hx
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul B.fields.E] at this
  unfold Formalism.L2.Forms.IsLocBasis
  refine forall_congr' fun x => iff_congr ⟨?_, ?_⟩ Iff.rfl
  · rintro ⟨s, hs, hx⟩
    refine ⟨B.T u * s, fun h => (hpP.dvd_mul.1 h).elim hpT hs, ?_⟩
    have h3 := hLN _ hx
    have e : ((B.T u * s : ℕ) : (I.rec7 l Z).host.E) • x = ((B.T u : ℕ) : (I.rec7 l Z).host.E) • ((s : (I.rec7 l Z).host.E) • x) := by
      rw [smul_smul, ← Nat.cast_mul]
    exact e ▸ h3
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, d.2.N_le_Lsh hx⟩

end GlobalTheory.DualOffLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientFieldFormOfPolynomialModelValue
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem form_of_rat_values : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls (i + 1) → ((I.rec7 l Z).chTw u μ).Y (i + 1) → ℂ, φ ∈ ((I.tw l l0 Z).fm u μ).Fi (i + 1) → (∀ c', ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = φ c') → ∃ x, ((I.tw l l0 Z).fm u μ).emb (i + 1) x = φ := by
  intro B X I _hOk _hPins l Z l0 Y O Pl Bs _hQp hStd _hBas _hBsLL _hUnf _hJets u μ i hi φ hφ hv
  have hlam : lamTG (D := I.rec7 l Z) (I.fm l u μ) (i + 1) = lamT (B.hcW u) (i + 1) := by
    funext τ
    show Formalism.L2.Forms.shW (Examples₂.lamOf (B.hcW u τ) (i+1)) (((i+1) * (B.R.t + 1) / 2 : ℕ) : ℤ) =
      GlobalTheory.Mem.Col2.shW (Examples₂.lamOf (B.hcW u τ) (i+1)) (-(((i+1 : ℕ) : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : (B.R.t + 1) / 2 = k + 1 := by omega
    have e2 : (i+1) * (B.R.t + 1) / 2 = (i+1) * (k + 1) := by
      rw [show B.R.t + 1 = (k + 1) * 2 by omega, ← mul_assoc, Nat.mul_div_cancel _ two_pos]
    unfold Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW
    congr 1
    funext j
    rw [e1, e2, Nat.cast_mul, sub_eq_add_neg]
  obtain ⟨nn, h1, -, h3, h4⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ ((I.tw l l0 Z).fm u μ) i hi
  change ∀ τ r, (lamTG (D := I.rec7 l Z) (I.fm l u μ) (i + 1) τ).natW r = _ at h3
  change ∀ τ, (lamTG (D := I.rec7 l Z) (I.fm l u μ) (i + 1) τ).detShift = _ at h4
  rw [hlam] at h3 h4
  have hnat : (fun τ r => (lamT (B.hcW u) (i + 1) τ).natW r) = extNu (B.R.N (i + 1)) (nuT (I.rec7 l Z) u i) := by
    funext τ r
    refine (h3 τ r).trans ?_
    congr 1
    funext τ' r'
    exact h1 τ' r'
  haveI hLL : Infinite B.LL := Infinite.of_injective (fun n : ℕ => (n : B.LL)) (fun a b h => by
    have := congrArg B.embLL h; simp only [map_natCast] at this; exact_mod_cast this)
  have hVV : Formalism.L2.DIV.VV B.LL (lamT (B.hcW u) (i + 1)) = polV (I.rec7 l Z) u (i + 1) := by
    rw [GlobalTheory.PdvKm.VV_eq_WtPol, hnat]; rfl
  have key : ∀ c', ∃ z : Formalism.L2.DIV.VV B.LL (lamT (B.hcW u) (i + 1)),
      evV B.fields.emb 1 (lamT (B.hcW u) (i + 1)) B.embLL z = φ c' := by
    intro c'
    obtain ⟨v', hv'⟩ := hv c'
    obtain ⟨⟨Q, hQ⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ v'
    refine ⟨⟨Q, hVV ▸ hQ⟩, ?_⟩
    rw [← hv']
    clear hnat h3 h1 hlam hφ hv hv'
    show _ = evP O u μ (i + 1) ⟨Q, hQ⟩
    funext y
    rw [evV_apply]
    show _ = (∏ τ, (((I.rec7 l Z).chTw u μ).de (i + 1) y τ) ^ (-(twB (I.rec7 l Z) u μ (i + 1) τ))) *
      GL3Theta.evFr (I.rec7 l Z) (MvPolynomial.map (I.rec7 l Z).what₂.embLL Q) ((O u μ).frm (i + 1) y)
    have hde : ∀ τ, ((I.rec7 l Z).chTw u μ).de (i + 1) y τ = (y.1 τ).det := fun τ => by
      rw [(O u μ).frm_de (i + 1) hi y τ, hStd.frm u μ (i + 1) y]
      rfl
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Matrix.one_mul, shiftOf, twB, GL3Theta.evFr, hStd.frm u μ (i + 1) y, hde, Pi.one_apply]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact congrArg (fun e : ℤ => (y.1 τ).det ^ e) (h4 τ)
  choose z hz using key
  let o : Frames (gramC (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (embAt B.embLL B.fields.emb)) :=
    ⟨fun _ => 1, fun τ => by simp⟩
  have hinv : ∀ c' (g : (I.stp u μ (i + 1)).Stab c'),
      (I.stp u μ (i + 1)).rho B.fields.emb (lamT (B.hcW u) (i + 1)) c'.1 g.1 (z c') = z c' := by
    intro c' g
    apply evV_injective B.fields.emb 1 (lamT (B.hcW u) (i + 1)) B.embLL o
    have e1 := Law.evV_rho (I.stp u μ (i + 1)) B.fields.emb B.embLL (lamT (B.hcW u) (i + 1)) c'.1 g.1 (z c')
    have e2 := (hφ c').2 g
    refine e1.trans ?_
    refine (congrArg ((I.stp u μ (i + 1)).tr B.fields.emb B.embLL c'.1 g.1) (hz c')).trans ?_
    exact e2.trans (hz c').symm
  refine ⟨⟨z, hinv⟩, ?_⟩
  funext c'
  exact hz c'

end GlobalTheory.Mem.Col2.TC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartFromAdelicDictionaryStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framed_chart_from_adelic_dictionary : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E hc.sig J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (e : ℕ) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (k t : GL (Fin n) (AfE F E)) (C : Type) (s : C → DecoF E n ST SG Q) (y : C → GL (Fin n) (AfE F E)) (stab : C → Type) [∀ c, Group (stab c)] (lat : C → Submodule (𝓞 E) (Fin n → E)) (gm : ∀ c, stab c →* UF E n) (ψ : topU S.U t Θ d →* ℂˣ), J = 1 → (∀ v, v ∈ Qv ↔ ∃ P ∈ Q, P.under (𝓞 F) = v) → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → (∀ P : Q, d P = ((qOf P.1 : ℕ) : E) ^ e) → k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ S.U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → (∀ c, IsPtOf hc (y c * (k * t)) (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = p) → (∀ c, lat c = (s c).deco.1.L) → (∀ c, Function.Injective (gm c)) → (∀ c (γ : UF E n), γ ∈ (gm c).range ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c) → (∀ x : topU S.U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → ψ x = 1) → ∃ C' : ClsG hc.sig J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))) stab lat, C'.lev.Lb = S.Lb ∧ C'.lev.U = topU S.U t Θ d ∧ (∀ v, v ∉ Qv → C'.lev.Uloc v = S.Uloc v) ∧ (∀ (x : C'.lev.U) (x' : S.U) (x'' : topU S.U t Θ d), x.1 = x'.1 → x.1 = x''.1 → C'.lev.chi x = S.chi x' * ψ x'') ∧ (∀ c, (C'.y c).1 = y c) ∧ ∀ c s, (C'.stabI c s).1 = ufGL E n (gm c s) := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.exists_clsG_top | exact GlobalTheory.Mem.Col2.TopCh.exists_clsG_top | (intros; apply GlobalTheory.Mem.Col2.TopCh.exists_clsG_top <;> assumption)
end

