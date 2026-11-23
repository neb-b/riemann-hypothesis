module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.ContractionsCovariantIff
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0012
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0013
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0015
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0009
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0015
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0021
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0023
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0020
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0022
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0019
public import Formalism.FormalDegreeBessel.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
public import Formalism.HermitianCurvature.StatementNF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeAction
section
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrD

section Left

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}

theorem mem_left (hD : IsDom k r z z' (Fin.last r) D) {g h : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D)
    (hh : h ∈ UWset k r z) : h * g ∈ Glev k r (Fin.last r) ∩ D := by
  obtain ⟨hgG, hgD⟩ := hg
  refine ⟨?_, ?_⟩
  · simp only [Glev, UH, UWset, Set.mem_setOf_eq] at hgG hh ⊢
    refine ⟨?_, fun a ha => ?_⟩
    · rw [conjTranspose_mul]
      calc gᴴ * hᴴ * Hpk k r * (h * g) = gᴴ * (hᴴ * Hpk k r * h) * g := by simp only [Matrix.mul_assoc]
        _ = Hpk k r := by rw [hh.1, hgG.1]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, (hgG.2 a ha).1, (hgG.2 a ha).2]
      exact hh.2.1 a
  · have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
    have h1N : (1 : Mx k r) ∈ Nlev k r (Fin.last r) := by simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
    have hS := hD.2 g ⟨hgG, hgD⟩ h ⟨h, hh, 1, h1N, by simp⟩ 1 ⟨1, h1z', 1, h1N, by simp⟩
    simpa using hS

theorem J_left (hπ : IsCRepOn (UWset k r z) π) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D) {g h : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hh : h ∈ UWset k r z) : J (h * g) = (π h).comp (J g) := by
  have h1z : (1 : Mx k r) ∈ UWset k r z := by simp [UWset, UH]
  have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
  simp only [FFl, Set.mem_setOf_eq] at hJ
  have e1 := hJ.2.2.2 g hg 1 h1z 1 h1z'
  have e2 := hJ.2.2.2 g hg h hh 1 h1z'
  rw [one_mul, mul_one, hπ.1] at e1
  have e1' : J g ∘SL π' 1 = J g := by
    ext x
    exact (congrArg (fun T => T x) e1).symm
  rw [mul_one] at e2
  rw [e2, e1']

theorem ld_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) {X : Mx k r} (hX : InLieW k r z X)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) : LdV X F g = (B.comp (dOp π X)).comp (J g) := by
  have hfun : (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) =
      fun t : ℝ => (B.comp (π (NormedSpace.exp ((t : ℂ) • X)))).comp (J g) := by
    funext t
    have hu := exp_uw hX t
    rw [hF _ (mem_left hD hg hu), J_left hπ hJ hg hu, ContinuousLinearMap.comp_assoc]
  unfold LdV
  rw [hfun]
  have hd := dOp_hasDeriv hπ hc hX
  let L : (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
    (((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (J g)).comp
      ((ContinuousLinearMap.compL ℂ Wp Wp Wp) B)).restrictScalars ℝ
  have key : HasDerivAt (fun t : ℝ => (B.comp (π (NormedSpace.exp ((t : ℂ) • X)))).comp (J g))
      ((B.comp (dOp π X)).comp (J g)) 0 := by
    have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    convert h2 using 1
    all_goals first | rfl | (ext; rfl)
  exact key.deriv

theorem lz_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) {Z : Mx k r}
    (h1 : InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    LZ (Hpk k r) Z F g = (B.comp (ecOp π Z)).comp (J g) := by
  unfold LZ
  rw [ld_left hD hπ hc hJ hF h1 hg, ld_left hD hπ hc hJ hF h2 hg]
  ext v
  simp [ecOp]

theorem fold_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, InLieW k r z (hpart1 (Hpk k r) p.2) ∧ InLieW k r z (hpart2 (Hpk k r) p.2)) :
    ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (B : Wp →L[ℂ] Wp), (∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) →
      ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ v,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) F g v =
          B ((L.map fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) := by
  induction L with
  | nil => intro F B hF g hg v; simp [hF g hg]
  | cons p L ih =>
    intro F B hF g hg v
    obtain ⟨h1, h2⟩ := hL p (by simp)
    have hF' : ∀ g ∈ Glev k r (Fin.last r) ∩ D,
        (p.1 • F + LZ (Hpk k r) p.2 F) g = (p.1 • B + B.comp (ecOp π p.2)).comp (J g) := by
      intro g hg
      rw [Pi.add_apply, Pi.smul_apply, lz_left hD hπ hc hJ hF h1 h2 hg, hF g hg]
      ext x
      simp
    have := ih (fun q hq => hL q (by simp [hq])) _ _ hF' g hg v
    simp only [List.map_cons, List.foldl_cons, List.foldr_cons]
    rw [this]
    simp [ecRep_eq hπ hc h1 h2]

end Left

end QrD

theorem left_type_action : Formalism.FourierDecayAlt.Q.LeftTypeAction := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D hz hz' hD hπ hc J hJ g hg Bs hB w v
  unfold capLft capRep qmFrev qmF
  have key : ∀ σ : Equiv.Perm (Fin m), ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ v,
      ((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
          fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) J g v =
        (ContinuousLinearMap.id ℂ Wp)
          (((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
            fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) :=
    fun σ => QrD.fold_left hD hπ hc hJ _ (by
      intro p hp
      simp only [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j) J (ContinuousLinearMap.id ℂ Wp) (fun g _ => by simp)
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul, ContinuousLinearMap.id_apply] at key
  simp only [id, Finset.sum_apply, Pi.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [key σ g hg v]

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
section
theorem Formalism.FourierDecayAlt.P.expansion_first_column : Formalism.FourierDecayAlt.Q.ExpFirstCol := PI.QmColExpWork.expFirstCol

theorem Formalism.FourierDecayAlt.P.expansion_last_column : Formalism.FourierDecayAlt.Q.ExpLastCol := PI.QmColExpWork.expLastCol

theorem Formalism.FourierDecayAlt.P.expansion_first_line : Formalism.FourierDecayAlt.Q.ExpFirstRow := PI.QmRowExpWork.expFirstRow_of quantum_minor_row_form

theorem Formalism.FourierDecayAlt.P.expansion_last_line : Formalism.FourierDecayAlt.Q.ExpLastRow := PI.QmRowExpWork.expLastRow_of quantum_minor_row_form

theorem Formalism.FourierDecayAlt.P.line_form_of_minor : Formalism.FourierDecayAlt.Q.RowForm := quantum_minor_row_form

theorem Formalism.FourierDecayAlt.P.skip_succ_identity : Formalism.FourierDecayAlt.Q.SkipSucc := PI.QmSkipWork.skipSucc

theorem Formalism.FourierDecayAlt.P.skip_succ_double_identity : Formalism.FourierDecayAlt.Q.SkipSucc2 := PI.QmSkipWork.skipSucc2

theorem Formalism.FourierDecayAlt.P.star_quantum_minor : Formalism.FourierDecayAlt.Q.StarMinor := quantum_minor_star

theorem Formalism.FourierDecayAlt.P.rtt_independence : Formalism.FourierDecayAlt.Q.RTTIndependence := rtt_independence'

theorem Formalism.FourierDecayAlt.P.contractions_covariant : Formalism.FourierDecayAlt.Q.ContractionsCovariant := PI.contractionsCovariant_iff.mpr ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩

theorem Formalism.FourierDecayAlt.P.first_contraction_adapted : Formalism.FourierDecayAlt.Q.ChatAdapted := (contraction_adapted Formalism.FourierDecayAlt.P.contractions_covariant).1

theorem Formalism.FourierDecayAlt.P.second_contraction_adapted : Formalism.FourierDecayAlt.Q.Chat2Adapted := (contraction_adapted Formalism.FourierDecayAlt.P.contractions_covariant).2

theorem Formalism.FourierDecayAlt.P.generator_gl_level : Formalism.FourierDecayAlt.Q.EabGlLev := qnEabGl

theorem Formalism.FourierDecayAlt.P.generator_action_preserved : Formalism.FourierDecayAlt.Q.EabPres := qnEabPres

theorem Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian : Formalism.FourierDecayAlt.Q.QMinorLeftH := quantum_minor_left

theorem Formalism.FourierDecayAlt.P.right_differential_skew : Formalism.FourierDecayAlt.Q.RdSkew := qnRdSkew

theorem Formalism.FourierDecayAlt.P.right_action_rule : Formalism.FourierDecayAlt.Q.RuleRight := qnRuleRight

theorem Formalism.FourierDecayAlt.P.weyl_level_element_properties : Formalism.FourierDecayAlt.Q.WeylLevelElementFacts := weyl_level_element_properties'

theorem Formalism.FourierDecayAlt.P.twisted_leibniz_rule : Formalism.FourierDecayAlt.Q.YLeibniz := qnYLeibniz
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSystemAdmissibleSize
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Finset

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem prod_lamCfg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Y : ℝ) : ∏ s, (Y + lamCfg S v s) = S.P v Y := by
  show ∏ s : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
      (Y + (S.G.place (S.pl v)).lam ((s : ℕ) + 1)) = (S.G.place (S.pl v)).P Y
  have hm : (S.G.place (S.pl v)).k + (S.G.place (S.pl v)).m - 1 =
      (D.parOf S v).k + 2 * (D.parOf S v).r + 1 := by
    show S.G.k + (2 * S.G.r + 2) - 1 = S.G.k + 2 * S.G.r + 1
    omega
  rw [Sz.Cfg.P, hm]
  have e1 : ∏ s : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
      (Y + (S.G.place (S.pl v)).lam ((s : ℕ) + 1)) =
      ∏ i ∈ Finset.range ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
        (Y + (S.G.place (S.pl v)).lam (i + 1)) :=
    Fin.prod_univ_eq_prod_range (fun i => Y + (S.G.place (S.pl v)).lam (i + 1)) _
  rw [e1, Finset.range_eq_Ico, Finset.prod_Ico_add' (fun i => Y + (S.G.place (S.pl v)).lam i), zero_add]
  rfl

theorem level_system_admissible_size (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (hA : D.AdmAt S v a)
    (hI : ∀ x ∈ a, x.2 ∈ Set.Icc (S.cutLo v) (S.cutHi v)) (l : ℕ)
    (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT) (c : LE.Cut) (Lb : ℝ) :
    (MA.sysQ (D.parOf S v) l L j (lamCfg S v) (S.cutLo v) (S.cutHi v) Lb c S.Ntop).admitted a ∧
      (MA.sysQ (D.parOf S v) l L j (lamCfg S v) (S.cutLo v) (S.cutHi v) Lb c S.Ntop).size a = S.sizeAt v a := by
  obtain ⟨w, rfl⟩ := hA
  refine ⟨⟨fun x hx => hI x hx, ?_⟩, ?_⟩
  · rw [List.pairwise_iff_getElem]
    intro i i' hi hi' hii
    have := w.2.1.2 v i i' hi hi' (Nat.ne_of_lt hii) 0 (by norm_num) (by norm_num)
    simpa using this
  · show ((w.1 v).map fun x => |∏ s, (x.2 + lamCfg S v s)|).prod = _
    rw [C.HidaSetting.sizeAt]
    simp only [prod_lamCfg]

end defs

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
section
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFRadRedA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Classical

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem uwb_glev {g : Q.Mx k r} (hg : g ∈ B2.UWb k r) : g ∈ Glev k r (Fin.last r) := ⟨hg.1, fun a _ => hg.2 a⟩

theorem glev_uwb {g : Q.Mx k r} (hg : g ∈ Glev k r (Fin.last r)) : g ∈ B2.UWb k r := ⟨hg.1, fun a => hg.2 a a.isLt⟩

theorem muZ_uwb (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    muZ k r μsec ζ ∈ B2.UWb k r := TwoByOneBlock.emb_mem_UWb (hsec.2 ζ hζ).1

theorem zeta_eq (g : Q.Mx k r) : zetaL k r z z' (Fin.last r) g = herm (Hpk k r) (g *ᵥ z') z := by
  simp [Q.zetaL, Formalism.QuantumDeterminants.fvec]

private theorem one_mem_uwset (w : Fin (2 * r + k + 1) → ℂ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r w := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp [UH]

theorem zeta_muZ (hz : inWb k r z) (hz' : inWb k r z') (hsec : IsSection k r z z' μsec) {ζ : ℂ}
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) : zetaL k r z z' (Fin.last r) (muZ k r μsec ζ) = ζ := by
  have h1 := one_mem_uwset (k := k) (r := r) z
  have h1' := one_mem_uwset (k := k) (r := r) z'
  have h2 := (TwoByOneBlock.rankOneMem k r z z' μsec hz hz' hsec ζ hζ 1 h1 1 h1').2
  rw [zeta_eq]
  simpa [NF.muZ] using h2

theorem qr_open : IsOpen (QR k r z z') := by
  have hO : IsOpen (OmX r) := by
    have he : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0} := by ext x; simp [OmX]
    rw [he]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  exact (hO.preimage continuous_fst).inter
    (isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd))

theorem mem_domR (hz : inWb k r z) (hz' : inWb k r z') (hsec : IsSection k r z z' μsec)
    {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QR k r z z') : (q.1, muZ k r μsec q.2) ∈ DomR k r z z' := by
  refine ⟨hq.1, uwb_glev (muZ_uwb hsec hq.2), ?_⟩
  show 0 < GGl k r z z' (muZ k r μsec q.2)
  unfold GGl
  rw [zeta_muZ hz hz' hsec hq.2]
  exact sub_pos.2 hq.2

theorem muZ_contDiffOn (hsec : IsSection k r z z' μsec) :
    ContDiffOn ℝ ∞ (fun ζ => muZ k r μsec ζ) {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ} := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  simp only [NF.muZ, B2.embWb]
  by_cases h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · simp only [dif_pos h]
    exact hsec.1 _ _
  · simp only [dif_neg h]
    exact contDiffOn_const

theorem decomp (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {g : Q.Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r z z' g) :
    ∃ h ∈ UWset k r z, ∃ h' ∈ UWset k r z', g = h * muZ k r μsec (zetaL k r z z' (Fin.last r) g) * h' := by
  have hU : g ∈ B2.UWb k r := glev_uwb hg
  have hζ : Tz k r z * Tz k r z' < Complex.normSq (herm (Hpk k r) (g *ᵥ z') z) := by
    have h2 := hG
    unfold GGl at h2
    rw [zeta_eq] at h2
    linarith
  obtain ⟨h, hh, h', hh', he⟩ := TwoByOneBlock.rankOneCoord k r z z' μsec hk hz hz' hT hT' hsec g hU hζ
  refine ⟨h⁻¹, BigCellInversePair.uw_inv hh, h', hh', ?_⟩
  rw [zeta_eq]
  exact he

theorem radRedMem : NF.RadRedMem := by
  intro Wp Wq _ _ _ _ k r z z' μsec π π' hB Φ hΦ
  obtain ⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩ := hB
  obtain ⟨h0, hs, he⟩ := hΦ
  refine ⟨?_, fun q hq => ?_, fun q hq => Set.indicator_of_notMem hq _⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro q0 hq0
    obtain ⟨V, F, hV, hxV, hF, hΦF⟩ := hs _ (mem_domR hz hz' hsec hq0)
    have hψ : ContDiffOn ℝ ∞ (fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2)) (QR k r z z') :=
      contDiffOn_fst.prodMk ((muZ_contDiffOn hsec).comp contDiffOn_snd (fun q hq => hq.2))
    refine ⟨QR k r z z' ∩ (fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2)) ⁻¹' V,
      hψ.continuousOn.isOpen_inter_preimage qr_open hV, ⟨hq0, hxV⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (F ∘ fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2))
        (QR k r z z' ∩ (QR k r z z' ∩ (fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2)) ⁻¹' V)) :=
      hF.comp (hψ.mono fun q hq => hq.1) fun q hq => hq.2.2
    refine hc.congr fun q hq => ?_
    simp only [radR, Set.indicator_of_mem hq.1, Function.comp_apply]
    exact hΦF _ hq.2.2 (uwb_glev (muZ_uwb hsec hq.1.2))
  · simp only [radR, Set.indicator_of_mem hq, Fib, Set.mem_setOf_eq]
    intro p hp
    obtain ⟨hp1, hp2, hpe⟩ := hp
    have h3 := he _ (mem_domR hz hz' hsec hq) p.1 hp1 p.2 hp2
    simp only at h3
    rw [hpe] at h3
    exact h3.symm

theorem radRedInj : NF.RadRedInj := by
  intro Wp Wq _ _ _ _ k r z z' μsec π π' hB Φ hΦ Ψ hΨ hR
  obtain ⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩ := hB
  obtain ⟨h0, -, he⟩ := hΦ
  obtain ⟨h0', -, he'⟩ := hΨ
  funext x g
  by_cases hx : (x, g) ∈ DomR k r z z'
  · obtain ⟨hxO, hg, hG⟩ := hx
    obtain ⟨h, hh, h', hh', hd⟩ := decomp hk hz hz' hT hT' hsec hg hG
    have hq : (x, zetaL k r z z' (Fin.last r) g) ∈ QR k r z z' := by
      refine ⟨hxO, ?_⟩
      have h2 := hG
      unfold GGl at h2
      linarith
    have hD := mem_domR hz hz' hsec hq
    have e1 := he _ hD h hh h' hh'
    have e2 := he' _ hD h hh h' hh'
    have hr := congrFun hR (x, zetaL k r z z' (Fin.last r) g)
    simp only [radR, Set.indicator_of_mem hq] at hr
    simp only at e1 e2 hd
    rw [hd, e1, e2, hr]
  · exact (h0 (x, g) hx).trans (h0' (x, g) hx).symm

end Formalism.FourierDecayAlt.P.NFRadRedA

namespace Formalism.FourierDecayAlt.P

theorem radical_reduction_mem : Formalism.FourierDecayAlt.NF.RadRedMem := NFRadRedA.radRedMem

theorem radical_reduction_injective : Formalism.FourierDecayAlt.NF.RadRedInj := NFRadRedA.radRedInj

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
section
namespace Formalism.FourierDecayAlt.P

theorem integration_formula_constant : Formalism.FourierDecayAlt.B2.IntConst :=
  integration_formula_of_parts iterated_integration_formula rank_one_integration_formula b2_conjInvRaw_proof opposite_weyl_haar_exists
    bruhat_big_cell_factorization unipotent_weyl_properties weight_factorization

theorem integration_formula_normalisation_unique : Formalism.FourierDecayAlt.B2.IntNorm :=
  integral_normalisation_from_constant integration_formula_constant

theorem normalisation_unique_every_setting : Formalism.FourierDecayAlt.B2.IntNormB :=
  normalisation_every_setting integration_formula_normalisation_unique

theorem norm_power_integrable_sharp : Formalism.FourierDecayAlt.B2.GNIntSharp :=
  norm_power_integrable_sharp_of_volume spherical_shell_integral matrix_norm_ge_one norm_ball_volume_sharp

theorem matrix_coefficient_integrable_all : Formalism.FourierDecayAlt.B2.CCIntAll :=
  matrix_coefficient_integrable_of_parts matrix_coefficient_bound_by_norm norm_power_integrable_sharp

namespace IntegrationFormulaNormalisation

theorem exists_both : Formalism.FourierDecayAlt.B2.RealPlaceDataExists ∧ Formalism.FourierDecayAlt.B2.RealPlaceDataNonempty :=
  Formalism.FourierDecayAlt.P.SettingConstruction.setting_exists_of_haar_normalisation Formalism.FourierDecayAlt.P.unitary_group_haar_exists Formalism.FourierDecayAlt.P.weyl_haar_exists
    Formalism.FourierDecayAlt.P.unipotent_haar_exists Formalism.FourierDecayAlt.P.integration_formula_normalisation_unique

end IntegrationFormulaNormalisation

theorem setting_with_prescribed_data_exists : Formalism.FourierDecayAlt.B2.RealPlaceDataExists :=
  Formalism.FourierDecayAlt.P.IntegrationFormulaNormalisation.exists_both.1

theorem lemma_b_from_xi : Formalism.FourierDecayAlt.B2.LemmaBFromXi :=
  Formalism.FourierDecayAlt.P.BesselScaling.lemmaBFromXi_of conjugation_invariance_every_setting dilation_jacobian_every_setting matrix_coefficient_integrable_all normalisation_unique_every_setting

end Formalism.FourierDecayAlt.P
end

