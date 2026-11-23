module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceFirstFactorLocalFrame
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFrameSecondFactorReversedDualBasis
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormNormsMinorsEqLabelProof
section
noncomputable section
open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm.HasLabelling
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frameExp_cast (r l : ℕ) (hl : l ≤ r + 1) :
    ((frameExp r l : ℕ) : ℤ) = ∑ a ∈ Finset.range l, ((r : ℤ) - a) := by
  induction l with
  | zero => simp [frameExp]
  | succ l ih =>
    have h1 : frameExp r (l + 1) = frameExp r l + (r + 1 - (l + 1)) := by
      unfold frameExp
      rw [Finset.sum_Icc_succ_top (by omega)]
    have h2 : ((r + 1 - (l + 1) : ℕ) : ℤ) = (r : ℤ) - l := by omega
    rw [h1, Nat.cast_add, ih (by omega), Finset.sum_range_succ, h2]

theorem nloc_eq (D : D7) (r l : ℕ) (x : D.host.E) :
    ((Nloc (ddS D) r l x : ℚ) : ℝ) =
      |((Algebra.norm ℚ x : ℚ) : ℝ)| * (Ideal.absNorm (dI D) : ℝ) ^ (-(2 * (frameExp r l : ℤ))) := by
  unfold Nloc
  rw [map_mul, FractionalIdeal.absNorm_span_singleton (𝓞 D.host.E), map_zpow₀,
    show ddS D = ((dI D : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) from rfl,
    FractionalIdeal.coeIdeal_absNorm]
  push_cast
  rfl

theorem norm_star (D : D7) (x : D.host.E) : Algebra.norm ℚ (star x) = Algebra.norm ℚ x := by
  have := Algebra.norm_eq_of_algEquiv ((starRingAut : D.host.E ≃+* D.host.E).toRatAlgEquiv) x
  simpa using this

theorem nloc_ne_zero (D : D7) (hd : dI D ≠ ⊥) (r l : ℕ) (x : D.host.E) :
    ((Nloc (ddS D) r l x : ℚ) : ℝ) ≠ 0 ↔ x ≠ 0 := by
  have hA : (Ideal.absNorm (dI D) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hd)
  rw [nloc_eq, mul_ne_zero_iff, abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]
  simp only [ne_eq, zpow_neg, inv_eq_zero, and_iff_left_iff_imp]
  intro _
  exact zpow_ne_zero _ hA

theorem T_eq {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
    (F G : Formalism.HermitianLatticeCounting.S6.FlagD H r) (h : G.e (Fin.last r) - F.e (Fin.last r) ∈ F.X) : G.T = F.T := by
  have hX : ∀ w : V, (∀ a : Fin r, H.B (F.e a.castSucc) w = 0) → ∀ y ∈ F.X, H.B y w = 0 := by
    intro w hw y hy
    have hle : F.X ≤ LinearMap.ker (H.B.flip w) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, -, rfl⟩
      simpa using hw b
    simpa using hle hy
  set x := G.e (Fin.last r) - F.e (Fin.last r) with hxdef
  have hxz : H.B x (F.e (Fin.last r)) = 0 := hX _ F.zperp x h
  have hzx : H.B (F.e (Fin.last r)) x = 0 := by rw [← H.herm, hxz, star_zero]
  have hxx : H.B x x = 0 := by
    refine hX x (fun a => ?_) x h
    have := hX (F.e a.castSucc) (fun b => F.iso b a) x h
    rw [← H.herm, this, star_zero]
  have hG : G.e (Fin.last r) = F.e (Fin.last r) + x := by rw [hxdef]; abel
  have h1 := G.zz
  rw [hG] at h1
  simp only [map_add (f := _), LinearMap.add_apply, hxz, hzx, hxx, F.zz, add_zero] at h1
  exact (neg_inj.1 h1).symm

end GlobalTheory.TypeAsm.HasLabelling

namespace GlobalTheory.TypeAsm
open GlobalTheory.TypeAsm.HasLabelling
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem labC : LabC := by
  intro D large₂ X Y u hS t N hN
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := by
    obtain ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩ := hS
    exact hH.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, hj, hDl, -, -, -⟩ :=
    GlobalTheory.DegAsm.adapt_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (Ft t) (dI D) N hN
  have hII : Formalism.HermitianLatticeCounting.S6.II (F0 X u) (Ft t) = Isp (lf D (X.Fu u)).fl (frq X t.rep).fl := nf_II _ _ _ _
  have hjT : N.j = jT t := by rw [hj, hII]; rfl
  have hjle : jT t ≤ D.R.rS := by unfold jT; omega
  have hnf : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l = star (Formalism.HermitianLatticeCounting.S6.Dl (F0 X u) (Ft t) l hl) :=
    fun l hl => nf_Dl _ _ _ _ l hl
  have hd : N.𝔡 = dI D := hN.1
  have hdne : dI D ≠ ⊥ := hd ▸ N.𝔡_ne
  have key : ∀ l, l ≤ jT t → N.nD l = ((Nloc (ddS D) D.R.rS l (labT t l) : ℚ) : ℝ) := by
    intro l hl
    have hl' : l ≤ D.R.rS + 1 := by omega
    have hlab : labT t l = star (Formalism.HermitianLatticeCounting.S6.Dl (F0 X u) (Ft t) l hl') := by
      simp only [labT, if_pos hl]
      exact hnf l hl'
    unfold GlobalTheory.DegCnt.NF.nD
    rw [dite_eq_left hl', hDl l hl', nloc_eq, hlab, norm_star, hd, frameExp_cast _ _ hl']
  refine ⟨hjT, ?_, ?_, ?_, ?_⟩
  · have hz : N.F.e (Fin.last D.R.rS) - (F0 X u).e (Fin.last D.R.rS) ∈ (F0 X u).X := hN.2.1 (Fin.last _)
    have h1 : ((N.T : ℕ) : D.host.E) = ((Tu D u : ℕ) : D.host.E) := by
      rw [← N.hT, T_eq (F0 X u) N.F hz]
      rfl
    exact_mod_cast h1
  · unfold GlobalTheory.DegCnt.NF.Del
    rw [hjT, key _ le_rfl]
    rfl
  · unfold GlobalTheory.DegCnt.NF.Db DbL
    rw [hjT]
    have hset : (Finset.Icc 1 (jT t)).filter (fun l => N.nD l ≠ 0) = k2ends D (jT t) (labT t) := by
      ext l
      simp only [k2ends, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, h2⟩, ?_⟩
        rw [key l h2] at h3
        exact (nloc_ne_zero D hdne _ _ _).1 h3
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, h2⟩, ?_⟩
        rw [key l h2]
        exact (nloc_ne_zero D hdne _ _ _).2 h3
    rw [hset]
    refine Finset.prod_congr rfl fun l hl => ?_
    have h2 : l ≤ jT t := by
      simp only [k2ends, Finset.mem_filter, Finset.mem_Icc] at hl
      exact hl.1.2
    exact key l h2
  · funext l
    unfold GlobalTheory.DegAsm.lab
    by_cases hl : l ≤ jT t
    · have hl' : l ≤ D.R.rS + 1 := by omega
      rw [dite_eq_left ⟨hl, hl'⟩]
      simp only [labT, if_pos hl]
      rw [hnf l hl', star_star]
    · rw [dite_eq_right (fun h => hl h.1)]
      simp only [labT, if_neg hl, star_zero]

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameLocalBasisUnitriangular
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem GlobalTheory.St.G.frame_local_basis_unitriangular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (k t : ℕ) (gp : Fin 2 → ℕ) (G : GLoc F E cm.sig gp) (L : Submodule (𝓞 E) (Fin n → E)) (Fr : AdFrame cm.sig J (hat F L) (gp 0 * gp 1) k), k = n → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, SplitsIn E (gp i)) → IsLat L → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal), SelfDualAt cm.sig J v L → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, G.phi i v hv (y b) = x b) ↔ ∀ b, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, (Fr.LocK L v y ↔ InJ n t n false (redM F v (G.mat i v hv fr y))) ∧ (Fr.LocK L v y → Fr.locChi v y = lamJ ψ (fun _ => 1) n t 0 n (redM F v (G.mat i v hv fr y))) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet k t gp G L Fr hk hpr hne hspl hlat i v hv _hsd
  subst k
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    refine ⟨1, G.psi0 i v hv, G.psi_zero_nontrivial_character i v hv, ?_, ?_⟩
    · intro x
      exact ⟨fun _ b => b.elim0, fun _ => ⟨0, zero_mem _, fun b => b.elim0⟩⟩
    · intro y _
      refine ⟨⟨fun _ => ⟨fun x => x.elim0, fun x => x.elim0, fun x => x.elim0, fun _ x => x.elim0⟩, fun _ i => i.elim0⟩, fun _ => ?_⟩
      simp only [AdFrame.locChi, supSum, lamJ, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, map_zero,
        Finset.range_zero, Finset.prod_empty, mul_one, AddChar.map_zero_eq_one]
      exact Fr.psi_int 0 (zero_mem _)
  · obtain ⟨-, hsplitv⟩ := _root_.GlobalTheory.St.G.SplitPrime.split_place F E cm (gp i) (hpr i) (hspl i)
    obtain ⟨-, hmax, -⟩ := hsplitv v hv
    obtain ⟨hmaxg, hgv, q, hq, hgq⟩ := _root_.GlobalTheory.St.G.TypePrimeProduct.uniformiser_prod F gp hpr hne i v hv hmax
    have hint := _root_.GlobalTheory.St.G.intV_iff_sp F E cm gp G hpr hspl i v hv
    obtain ⟨he1, he2, he3, he4, hb, hbd, hbe, hbde, hdual, hspan⟩ :=
      GlobalTheory.T.adelicLatticeFrame_component_localFrame F E cm.sig n J L (gp 0 * gp 1) n Fr v
    have hcase := _root_.GlobalTheory.St.G.local_idempotent_cases F E cm.sig n v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv)
      (gp 0 * gp 1) hgv L hlat hpos _ he1 he2 he4
    have hne0 : prV (E := E) v Fr.eps ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hcase
      rcases hcase with h | h <;> simp [Prod.ext_iff] at h
    obtain ⟨a, ha, hpa⟩ := GlobalTheory.T.standardAdditiveCharacter_local_ne_one_splitPrime F E cm Fr.psi Fr.psi_add Fr.psi_int Fr.psi_rat (gp i) (hpr i) (hspl i)
      v hv _ he3 he1 hne0
    have hnt : ∃ a ∈ intV E v, Fr.psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F)
        (((gp 0 * gp 1 : ℕ) : F)⁻¹) * (prV (E := E) v Fr.eps * a))) ≠ 1 := by
      refine ⟨(q : E ⊗[F] v.adicCompletion F) * a, mul_mem (natCast_mem _ q) ha, ?_⟩
      have hq0 : (q : F) ≠ 0 := by exact_mod_cast hq.ne'
      have hp0 : ((gp i : ℕ) : F) ≠ 0 := by exact_mod_cast (hpr i).ne_zero
      have key : algebraMap F (E ⊗[F] v.adicCompletion F) (((gp 0 * gp 1 : ℕ) : F)⁻¹) *
          (prV (E := E) v Fr.eps * ((q : E ⊗[F] v.adicCompletion F) * a)) =
          algebraMap F (E ⊗[F] v.adicCompletion F) (((gp i : ℕ) : F)⁻¹) * (prV (E := E) v Fr.eps * a) := by
        rw [← map_natCast (algebraMap F (E ⊗[F] v.adicCompletion F)) q, mul_left_comm (prV (E := E) v Fr.eps),
          ← mul_assoc, ← map_mul]
        have hcast : ((gp 0 * gp 1 : ℕ) : F) = ((gp i : ℕ) : F) * (q : F) := by rw [hgq]; push_cast; ring
        congr 2
        rw [hcast]
        field_simp
      rw [key]
      exact hpa
    rcases hcase with hc | hc
    · exact _root_.GlobalTheory.St.G.FirstFactorFrame.local_frame_first_factor F E cm n J hJ hdet t v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) hint (gp 0 * gp 1) hmaxg L hlat _ hc _ _ hb hbd hbe hbde hdual hspan Fr.psi Fr.psi_add Fr.psi_int hnt
    · exact _root_.GlobalTheory.St.G.local_frame_second_factor F E cm n J hJ hdet t v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) hint (gp 0 * gp 1) hmaxg L hlat _ hc _ _ hb hbd hbe hbde hdual hspan Fr.psi Fr.psi_add Fr.psi_int hnt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicKernelConvergenceProperties
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KernelConv

theorem coef_inv {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H) (g : UJ ε) :
    ⟪w, σ (uMat g⁻¹) w⟫_ℂ = star ⟪w, σ (uMat g) w⟫_ℂ := by
  obtain ⟨⟨h1, hmul⟩, hnorm, -⟩ := hσ
  have hg : uMat g ∈ UJset ε := g.2
  have hgi : uMat g⁻¹ ∈ UJset ε := (g⁻¹).2
  have hone : uMat g * uMat g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    simp
  have hback : σ (uMat g) (σ (uMat g⁻¹) w) = w := by
    have := congrArg (fun T : H →L[ℂ] H => T w) (hmul _ hg _ hgi)
    simp only [hone, h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
    exact this.symm
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ (uMat g) : H →ₗ[ℂ] H), norm_map' := hnorm _ hg }
  have key : ⟪w, σ (uMat g⁻¹) w⟫_ℂ = ⟪σ (uMat g) w, w⟫_ℂ := by
    rw [← L.inner_map_map w (σ (uMat g⁻¹) w)]
    show ⟪σ (uMat g) w, σ (uMat g) (σ (uMat g⁻¹) w)⟫_ℂ = _
    rw [hback]
  rw [key, ← inner_conj_symm]
  rfl

theorem phe_inv (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (hd : IsDSData B d) (x : B.I.GA) :
    phe B d x⁻¹ = star (phe B d x) := by
  have he : B.e x⁻¹.2 = star (B.e x.2) := B.e_adm.2.2.1 x.2
  have hp : ∏ v, ⟪B.w v, B.σ v (uMat (x⁻¹.1 v)) (B.w v)⟫_ℂ =
      star (∏ v, ⟪B.w v, B.σ v (uMat (x.1 v)) (B.w v)⟫_ℂ) := by
    rw [star_prod]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    show ⟪B.w v, B.σ v (uMat (x.1 v)⁻¹) (B.w v)⟫_ℂ = _
    exact coef_inv (hd v).2.1.2.2.1 (B.w v) (x.1 v)
  unfold phe ph
  rw [he, hp]
  simp only [star_mul', star_star]
  rw [show star ((∏ v, d v : ℝ) : ℂ) = ((∏ v, d v : ℝ) : ℂ) from Complex.conj_ofReal _]

theorem kern_eq (I : AutInst) (Γ : Subgroup I.GA) (hΓ : (Γ : Set I.GA) = I.GFset) (φ : I.GA → ℂ) (x y : I.GA) :
    kern I φ x y = ∑' γ : Γ, φ (x⁻¹ * γ.1 * y) := by
  unfold kern
  exact ((Equiv.subtypeEquivRight (fun a => by rw [← hΓ, SetLike.mem_coe]) : Γ ≃ I.GFset).tsum_eq
    (fun γ : I.GFset => φ (x⁻¹ * γ.1 * y))).symm

theorem kern_invariant (I : AutInst) (φ : I.GA → ℂ) (γ : I.GA) (hγ : γ ∈ I.GFset) (x y : I.GA) :
    kern I φ (γ * x) y = kern I φ x y ∧ kern I φ x (γ * y) = kern I φ x y := by
  have hΓ : ((GlobalTheory.RatDiscrete.ratSub I : Subgroup I.GA) : Set I.GA) = I.GFset := rfl
  have hγΓ : γ ∈ GlobalTheory.RatDiscrete.ratSub I := hγ
  rw [kern_eq I _ hΓ, kern_eq I _ hΓ, kern_eq I _ hΓ]
  constructor
  · refine ((Equiv.mulLeft (⟨γ, hγΓ⟩ : GlobalTheory.RatDiscrete.ratSub I)).tsum_eq
      (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ ((γ * x)⁻¹ * δ.1 * y))).symm.trans ?_
    congr 1; funext δ; simp [mul_assoc]
  · refine ((Equiv.mulRight (⟨γ, hγΓ⟩ : GlobalTheory.RatDiscrete.ratSub I)⁻¹).tsum_eq
      (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ (x⁻¹ * δ.1 * (γ * y)))).symm.trans ?_
    congr 1; funext δ; simp [mul_assoc]

theorem kern_symm (I : AutInst) (φ : I.GA → ℂ) (hφ : ∀ x, φ x⁻¹ = star (φ x)) (x y : I.GA) :
    kern I φ y x = star (kern I φ x y) := by
  have hΓ : ((GlobalTheory.RatDiscrete.ratSub I : Subgroup I.GA) : Set I.GA) = I.GFset := rfl
  rw [kern_eq I _ hΓ, kern_eq I _ hΓ, tsum_star]
  refine ((Equiv.inv (GlobalTheory.RatDiscrete.ratSub I)).tsum_eq
    (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ (y⁻¹ * δ.1 * x))).symm.trans ?_
  congr 1; funext δ
  rw [← hφ]
  simp [mul_assoc]

theorem kernelA : KernelA := by
  unfold KernelA
  intro B d h hd hn hL hH
  refine ⟨_root_.GlobalTheory.Dec.kernel_abs_bound B d h hd hn hL hH, _root_.GlobalTheory.Dec.continuous_kern_phe B d h hd hn hL hH, ?_, ?_⟩
  · intro γ hγ x y
    exact kern_invariant B.I (phe B d) γ hγ x y
  · intro x y
    exact kern_symm B.I (phe B d) (phe_inv B d hd) x y

end GlobalTheory.KernelConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseLatticeConstructionHolds
section
noncomputable section
open scoped Classical Pointwise
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm

namespace GlobalTheory.TypeAsm.LatticeOrthogonalComplement

section Gen
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {HW : Formalism.HermitianLatticeCounting.S6.HermSpace K W} {r : ℕ}

theorem B_swap {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

theorem X_B_e (F : FlagD H r) (a : Fin (r + 1)) (x : V) (hx : x ∈ F.X) : H.B x (F.e a) = 0 := by
  have key : ∀ b : Fin r, H.B (F.e b.castSucc) (F.e a) = 0 := by
    intro b
    induction a using Fin.lastCases with
    | last => exact F.zperp b
    | cast c => exact F.iso b c
  have : F.X ≤ LinearMap.ker (H.B.flip (F.e a)) := by
    unfold FlagD.X FlagD.Xa
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    simpa using key b
  simpa using this hx

theorem X_B_perp (F : FlagD H r) {v : V} (hv : ∀ a : Fin (r + 1), H.B (F.e a) v = 0) (x : V) (hx : x ∈ F.X) :
    H.B x v = 0 := by
  have : F.X ≤ LinearMap.ker (H.B.flip v) := by
    unfold FlagD.X FlagD.Xa
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    simpa using hv b.castSucc
  simpa using this hx

theorem flag_vector_mem_base_lattice (F : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F := by
  unfold V0
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))
  | cast c => exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨c, c.2, rfl⟩))

theorem mem_wSp (F : FlagD H r) (v : V) : v ∈ wSp F F ↔ ∀ a, H.B (F.e a) v = 0 := by
  rw [wSp, mem_perp_iff]
  constructor
  · intro h a
    exact B_swap (h _ (flag_vector_mem_base_lattice F a))
  · intro h x hx
    apply B_swap
    have : V0 F F ≤ LinearMap.ker (H.B.flip v) := by
      unfold V0
      refine sup_le (sup_le ?_ ?_) (Submodule.span_le.2 ?_)
      · intro y hy; simpa using X_B_perp F h y hy
      · intro y hy; simpa using X_B_perp F h y hy
      · rintro _ (rfl | rfl) <;> simpa [FlagD.z] using h (Fin.last r)
    simpa using this hx

theorem mem_perp_lattice_flag_iff (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (v : V) :
    v ∈ flagPairDefinitePartLattice F F Λ ↔ v ∈ Λ ⊔ rs (𝓞 K) F.X ∧ v ∈ wSp F F := by
  simp only [flagPairDefinitePartLattice, latL, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, h1⟩, h2⟩
    rw [uPerp, mem_perp_iff]
    rw [wSp, mem_perp_iff] at h2
    exact fun x hx => h2 x ((le_sup_left : F.X ⊔ F.X ≤ V0 F F) hx)

variable {F : FlagD H r} {e : W →ₗ[K] V}

theorem e_perp (hE : IsEmb F HW e) (w : W) (a : Fin (r + 1)) : H.B (F.e a) (e w) = 0 :=
  (hE.2 _).2 (Submodule.mem_sup_left ⟨w, rfl⟩) a

theorem e_wSp (hE : IsEmb F HW e) (w : W) : e w ∈ wSp F F := (mem_wSp F _).2 (e_perp hE w)

theorem X_wSp (x : V) (hx : x ∈ F.X) : x ∈ wSp F F :=
  (mem_wSp F _).2 fun a => B_swap (X_B_e F a x hx)

theorem decomp (hE : IsEmb F HW e) {v : V} (hv : v ∈ wSp F F) : ∃ w, v - e w ∈ F.X := by
  obtain ⟨_, ⟨w, rfl⟩, z, hz, h⟩ := Submodule.mem_sup.1 ((hE.2 v).1 ((mem_wSp F v).1 hv))
  exact ⟨w, by rw [← h]; simpa using hz⟩

theorem XB_e (hE : IsEmb F HW e) (x : V) (hx : x ∈ F.X) (w : W) : H.B x (e w) = 0 :=
  X_B_perp F (e_perp hE w) x hx

theorem memL_e (hE : IsEmb F HW e) (Λ : Submodule (𝓞 K) V) (w : W) :
    e w ∈ flagPairDefinitePartLattice F F Λ ↔ w ∈ lat0 F e Λ :=
  (mem_perp_lattice_flag_iff F Λ _).trans ⟨fun h => h.1, fun h => ⟨h, e_wSp hE w⟩⟩

theorem X_L (Λ : Submodule (𝓞 K) V) (x : V) (hx : x ∈ F.X) : x ∈ flagPairDefinitePartLattice F F Λ :=
  (mem_perp_lattice_flag_iff F Λ x).2 ⟨Submodule.mem_sup_right hx, X_wSp x hx⟩

theorem quotEquiv (hE : IsEmb F HW e) (Λ : Submodule (𝓞 K) V)
    (hspan : Submodule.span K (flagPairDefinitePartLattice F F Λ : Set V) = wSp F F) :
    Nonempty ((↥(Formalism.HermitianLatticesTheory.dual HW.B.flip (lat0 F e Λ)) ⧸
        (lat0 F e Λ).comap (Formalism.HermitianLatticesTheory.dual HW.B.flip (lat0 F e Λ)).subtype) ≃ₗ[𝓞 K]
      (↥(dual H (flagPairDefinitePartLattice F F Λ)) ⧸ (flagPairDefinitePartLattice F F Λ).comap (dual H (flagPairDefinitePartLattice F F Λ)).subtype)) := by
  set L := flagPairDefinitePartLattice F F Λ with hL
  set M := lat0 F e Λ with hM
  set DW := Formalism.HermitianLatticesTheory.dual HW.B.flip M with hDW
  set DV := dual H L with hDV
  have hmemW : ∀ w, w ∈ DW ↔ ∀ y ∈ M, HW.B w y ∈ (1 : Submodule (𝓞 K) K) := fun w => by
    rw [hDW, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    simp only [LinearMap.flip_apply]
  have hin : ∀ w : DW, e w ∈ DV := by
    rintro ⟨w, hw⟩
    rw [hDV, mem_dual_iff, hspan]
    refine ⟨e_wSp hE w, fun x hx => ?_⟩
    obtain ⟨w', hw'⟩ := decomp hE ((mem_perp_lattice_flag_iff F Λ x).1 hx).2
    have hw'M : w' ∈ M := (memL_e hE Λ w').1 (by simpa using L.sub_mem hx (X_L Λ _ hw'))
    have h1 : H.B (e w) x = HW.B w w' := by
      have e1 : x = e w' + (x - e w') := by abel
      rw [e1, map_add (f := _), B_swap (XB_e hE _ hw' w), add_zero, hE.1]
    rw [h1]
    exact (hmemW w).1 hw w' hw'M
  let f : DW →ₗ[𝓞 K] DV :=
    LinearMap.codRestrict DV ((e.restrictScalars (𝓞 K)).comp DW.subtype) (fun w => hin w)
  let Φ := (L.comap DV.subtype).mkQ ∘ₗ f
  have hker : LinearMap.ker Φ = M.comap DW.subtype := by
    ext w
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.mem_comap]
    exact memL_e hE Λ w
  have hsurj : Function.Surjective Φ := by
    intro q
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    have hv' := (mem_dual_iff H L v).1 hv
    rw [hspan] at hv'
    obtain ⟨w, hw⟩ := decomp hE hv'.1
    have hwD : w ∈ DW := (hmemW w).2 fun y hy => by
      have h1 : HW.B w y = H.B v (e y) := by
        rw [← hE.1]
        have e1 : v = e w + (v - e w) := by abel
        conv_rhs => rw [e1]
        rw [map_add (f := _), LinearMap.add_apply, XB_e hE (v - e w) hw y, add_zero]
      rw [h1]
      exact hv'.2 _ ((memL_e hE Λ y).2 hy)
    refine ⟨⟨w, hwD⟩, ?_⟩
    show Submodule.Quotient.mk (f ⟨w, hwD⟩) = Submodule.Quotient.mk ⟨v, hv⟩
    rw [Submodule.Quotient.eq]
    show e w - v ∈ L
    have := L.neg_mem (X_L Λ _ hw)
    simpa using this
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)⟩

end Gen

end GlobalTheory.TypeAsm.LatticeOrthogonalComplement

open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm
open LatticeOrthogonalComplement
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lat0C : LatticeNormalizationCondition := by
  intro D large₂ X Y u hS W HW hE Λ hΛ
  obtain ⟨hCM, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := _root_.GlobalTheory.TypeAsm.hostC D large₂ hS
  obtain ⟨N, hF, hF', -, hT, -, hTerm, -, -⟩ := _root_.GlobalTheory.IdNF.idNFC_holds D large₂ X Y u hS Λ (Or.inl hΛ)
  have hg1 : 1 ≤ gS D := by omega
  obtain ⟨-, -, -, hLat, -, hNe⟩ := GlobalTheory.DegCnt.PrimPerp.main _ _ (HV D) hCM D.R.rS N (gS D) Λ hg1 hTerm
  rw [hF, hF'] at hLat hNe
  rw [hT] at hNe
  have hAd : Adapt (F0 X u) (F0 X u) N.𝔡 N := by
    have := adapt_self N
    rwa [hF, hF'] at this
  obtain ⟨⟨hInt, -⟩, -⟩ := GlobalTheory.DegAsm.isDat_datOf _ _ _ (HV D) HW W.subtype hCM D.R.rS (F0 X u) (F0 X u) N.𝔡 N
    (gS D) Λ hg1 hE hAd hTerm
  have hd : (datOf (F0 X u) (F0 X u) W.subtype (gS D) Λ).1 = lat0 (F0 X u) W.subtype Λ := by
    ext w
    change W.subtype w ∈ flagPairDefinitePartLattice (F0 X u) (F0 X u) Λ ⊔ rs _ (F0 X u).X ↔ w ∈ lat0 (F0 X u) W.subtype Λ
    rw [sup_eq_left.2 (fun x hx => X_L Λ x hx), memL_e hE Λ]
  refine ⟨hd ▸ hInt, ?_⟩
  obtain ⟨q⟩ := quotEquiv hE Λ hLat.2
  obtain ⟨i⟩ := hNe
  exact ⟨q.trans i⟩

end GlobalTheory.TypeAsm
end
end

