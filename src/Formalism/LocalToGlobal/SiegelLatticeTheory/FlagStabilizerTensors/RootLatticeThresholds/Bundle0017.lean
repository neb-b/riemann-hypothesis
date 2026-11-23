module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0010
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsEv
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsCut Formalism.FourierDecayAlt

namespace Formalism.L2.SG.LoopsEv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section One

variable {D : D7} {large₂ : SizeData₂ D} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem loopsAmp_at {C' Cl Cg cb Cw cT CT C0 A C K₀ A₀ : ℝ}
    (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A) (hT : ConcTie X Y) (hA : (Y.tO u u').AbsConv)
    (hC : 1 ≤ C) (hCT : CT ≤ C) (hK₀ : K₀ ≤ C') (hA₀1 : 1 ≤ A₀) (hCl4 : 4 ≤ Cl)
    (hClA : 3 + 6 * Real.log (3 * A₀) ≤ Cl)
    (hXiH : Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v (NT D u)
      (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C))
    (HS : ∀ s, 2 ≤ s → s ≤ D.R.k → ClassLe (Y.tO u u') (bigS (Y.tO u u') s)
      (A₀ * rowS C D.R.k D.R.rS D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
        (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) * ddC X Y u u'))
    (H1 : ClassLe (Y.tO u u') ((Y.tO u u').nsc (Y.tO u u').genSet)
      (A₀ * oneT C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (GamS D large₂) * ddC X Y u u')) :
    ∃ (Al NT' Gam : ℝ) (Xi : ℕ → ℝ), 1 ≤ Al ∧
      Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v NT' Gam ∧
      Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v NT' Xi ∧
      6 * Real.log (3 * Al) ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k ∧
      Formalism.L2.SG.RowsOther.LoopsAmp (Y.tO u u') Al C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v Gam Xi
        (ddC X Y u u') := by
  have hP := params_at hH.1 X u hCl4 hCT hC hK₀
  obtain ⟨hn1, hn2, hn3⟩ := hyp_nums hH.1
  have hL := Formalism.MainNotions.BridgeLemma.d_one_le_L D large₂
  have hM := unitM_nonneg D large₂
  have hCG := large₂.CGam_pos
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = GamS D large₂ / gamCap D large₂ C := ⟨_, rfl⟩
  have hρe : ρ = Real.exp ((large₂.CGam - min large₂.CGam C) * unitM D large₂) := by rw [hρ, gam_ratio]
  have hmin0 : 0 ≤ min large₂.CGam C := le_min hCG.le (by linarith)
  have hlogρ : Real.log ρ ≤ (D.R.k : ℝ) / 8 := by
    rw [hρe, Real.log_exp]
    have e1 : (large₂.CGam - min large₂.CGam C) * unitM D large₂ ≤ large₂.CGam * unitM D large₂ :=
      mul_le_mul_of_nonneg_right (by linarith) hM
    linarith
  have hρ1 : 1 ≤ ρ := by
    rw [hρe]; exact Real.one_le_exp (mul_nonneg (by linarith [min_le_left large₂.CGam C]) hM)
  have hρ0 : 0 ≤ ρ := by linarith
  have hGr : GamS D large₂ = ρ * gamCap D large₂ C := by
    rw [hρ]; field_simp [(gamCap_pos D large₂ C).ne']
  have hdd := dd_nonneg hT u u'
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b D large₂
  have hb0 : (0 : ℝ) < large₂.sc.b := by linarith
  have hg : 0 < (X.B.g : ℝ) := by
    have h5 : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (X.B.g : ℝ) := hP.2.2.2.2.1
    have h8 : 0 < ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by positivity
    linarith
  have hv : 0 ≤ D.host.v := by linarith [hP.2.2.2.2.2.2.1]
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hGc0 : 0 ≤ gamCap D large₂ C := (gamCap_pos D large₂ C).le
  refine ⟨A₀ * ρ ^ 3, NT D u, gamCap D large₂ C, Formalism.MainNotions.BridgeLemma.XiB D large₂ u C,
    one_le_mul_of_one_le_of_one_le hA₀1 (one_le_pow₀ hρ1), hP, hXiH,
    log_size hk1 hL hn3 hn2 hClA hA₀1 hρ1 hlogρ, ?_⟩
  refine loopsAmp_of_classes (Y.tO u u') (A₀ * ρ ^ 3) C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v
    (gamCap D large₂ C) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) (ddC X Y u u') hA.2.2.le hA.2.1 (corank_le_k Y u u') ?_ ?_
  · intro s hs2 hsk
    have hB := HS s hs2 hsk
    rw [hGr] at hB
    have hX0 := xi_nonneg hXiH s hs2 hsk
    have hnd : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v
        (gamCap D large₂ C) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) := ndRow_nonneg hC0 hb0 hg hv hGc0 hX0
    have hdg : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v
        (gamCap D large₂ C) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) := degRow_nonneg hC0 hb0 hg hv hGc0 hX0
    have hsc := rowS_scale C D.R.k D.R.rS D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (gamCap D large₂ C) ρ
      (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) hρ1 hnd
    have hrow0 : 0 ≤ rowS C D.R.k D.R.rS D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (gamCap D large₂ C)
        (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) := by
      unfold rowS; exact add_nonneg hnd (mul_nonneg (sq_nonneg _) hdg)
    exact le_trans hB (scale_le hA₀1 le_rfl hdd hsc hrow0 hρ0)
  · have hB := H1
    rw [hGr] at hB
    have h0 : 0 ≤ oneT C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (gamCap D large₂ C) := oneT_nonneg hC0 hb0 hGc0
    have hsc := oneT_scale C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (gamCap D large₂ C) ρ hρ1 h0
    exact le_trans hB (scale_le hA₀1 le_rfl hdd hsc h0 hρ0)

end One

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
  (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt (Fm.D x i) (At x hx i))

end Fam

end Formalism.L2.SG.LoopsEv
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PvalFormExists
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} {hF : FinX Y} (W : WittDat X)
  (hI : SIso D.s (sOf hF))

theorem tc_pfst {u u' : D.what₂.Word} (p : D.s.Pair u u') : tc hI (D.s.pfst p) = (hI.eP u u' p).1.1 :=
  hI.pfst p

theorem tc_psnd {u u' : D.what₂.Word} (p : D.s.Pair u u') : tc hI (D.s.psnd p) = (hI.eP u u' p).1.2 :=
  hI.psnd p

theorem wRowOf_eq (hW : WRowIso D) {u u' : D.what₂.Word} (p : D.s.Pair u u') :
    wRowOf W hI p = Formalism.MainNotions.S.wRow D (X.Fu u) (hI.eP u u' p).1.1.lam := by
  unfold wRowOf FlagOfWord lamOf
  refine (hW (W.δ u) (W.isom u) (X.Fu u) _).trans ?_
  rw [tc_pfst]

theorem jtOf_eq {u u' : D.what₂.Word} (t : D.s.Term u u') (s : Formalism.L2.SG.PackageTie2.TT Y u u') (hs : s.toTerm = tc hI t) :
    ∃ g : fib Y (tc hI t), JtOf hI t = amp Y g.1 := by
  have h : ∃ s : Formalism.L2.SG.PackageTie2.TT Y u u', s.toTerm = tc hI t := ⟨s, hs⟩
  exact ⟨⟨h.choose, h.choose_spec⟩, by unfold JtOf; rw [dite_eq_left h]⟩

theorem pair_form (hW : WRowIso D) (hC : AmpCov Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF)
    (u u' : D.what₂.Word) (p : D.s.Pair u u') :
    ∃ (c : ℂ) (U : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'), ‖c‖ = 1 ∧
      D.s.pval p = (wRowOf W hI p : ℂ) * c *
        Formalism.MainNotions.S.hsInner ((JtOf hI (D.s.pfst p)).comp (cl U)) (JtOf hI (D.s.psnd p)) := by
  have h1 := tc_pfst hI p
  have h2 := tc_psnd hI p
  obtain ⟨g₁, hg₁⟩ := jtOf_eq hI (D.s.pfst p) (hI.eP u u' p).2.choose.1
    ((hI.eP u u' p).2.choose.2.trans h1.symm)
  obtain ⟨g₂, hg₂⟩ := jtOf_eq hI (D.s.psnd p) (hI.eP u u' p).2.choose_spec.choose.1
    ((hI.eP u u' p).2.choose_spec.choose.2.trans h2.symm)
  obtain ⟨c, U, hc, hv⟩ := pvR_form hF hC hK hN (hI.eP u u' p) ⟨g₁.1, g₁.2.trans h1⟩ ⟨g₂.1, g₂.2.trans h2⟩
  refine ⟨c, U, hc, ?_⟩
  rw [hI.pval p, wRowOf_eq W hI hW p, hg₁, hg₂]
  exact hv

theorem pvalForm_exists (hW : WRowIso D) (hC : AmpCov Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF) :
    ∃ A : AmpDat X, PvalForm W hI A := by
  have H := fun (u u' : D.what₂.Word) (p : D.s.Pair u u') => pair_form W hI hW hC hK hN u u' p
  choose c U hc hv using H
  exact ⟨{ chi := fun {u u'} p => c u u' p
           chi_norm := fun {u u'} p => hc u u' p
           piB := fun {u u'} p => cl (U u u' p)
           piB_unit := fun {u u'} p x => (U u u' p).norm_map x },
    fun {u u'} p => hv u u' p⟩

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittExistsHolds
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Flag

variable {D : D7} {T : D.host.E}

theorem flag_span_orth (F : FlagG (VS D) D.R.rS T) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range F.e)) : (VS D).hT x F.z = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact F.z_orth a
  | zero => simp
  | add y w _ _ hy hw => simp [hy, hw]
  | smul c y _ hy => simp [hy]

theorem flag_fvec_indep (hT : T ≠ 0) (F : FlagG (VS D) D.R.rS T) : LinearIndependent D.host.E F.fvec := by
  unfold FlagG.fvec
  rw [linearIndependent_finSnoc]
  refine ⟨F.e_indep, fun hz => hT ?_⟩
  have h1 := flag_span_orth F hz
  rw [F.z_norm] at h1
  exact neg_eq_zero.1 h1

theorem flag_gram {T' : D.host.E} (hTT : T = T') (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T')
    (i j : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec i) (F.fvec j) = (VS D).hT (F'.fvec i) (F'.fvec j) := by
  subst hTT
  have hze : ∀ (G : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS), (VS D).hT G.z (G.e a) = 0 := by
    intro G a
    rw [← (VS D).herm.eq (G.e a) G.z, G.z_orth a, map_zero]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp only [FlagG.fvec, Fin.snoc_last, F.z_norm, F'.z_norm]
    | cast b => simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc, hze]
  | cast a =>
    induction j using Fin.lastCases with
    | last => simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc, F.z_orth, F'.z_orth]
    | cast b => simp only [FlagG.fvec, Fin.snoc_castSucc, F.e_iso, F'.e_iso]

theorem flag_witt {T' : D.host.E} (hT : T ≠ 0) (hTT : T = T') (F : FlagG (VS D) D.R.rS T)
    (F' : FlagG (VS D) D.R.rS T') :
    ∃ δ : (VS D).V ≃ₗ[D.host.E] (VS D).V, δ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, δ (F.e a) = F'.e a) ∧
      δ F.z = F'.z := by
  have hind := flag_fvec_indep hT F
  have hind' := flag_fvec_indep (hTT ▸ hT) F'
  set U := Submodule.span D.host.E (Set.range F.fvec) with hU
  let b : Module.Basis (Fin (D.R.rS + 1)) D.host.E U := Module.Basis.span hind
  let f : U →ₗ[D.host.E] (VS D).V :=
    Finsupp.linearCombination D.host.E F'.fvec ∘ₗ (b.repr : U →ₗ[D.host.E] (Fin (D.R.rS + 1) →₀ D.host.E))
  have hfb : ∀ i, f (b i) = F'.fvec i := by
    intro i
    simp [f, Module.Basis.repr_self, Finsupp.linearCombination_single]
  have hbv : ∀ i, ((b i : U) : (VS D).V) = F.fvec i := by
    intro i
    exact congrArg Subtype.val (Module.Basis.span_apply hind i)
  have hinj : Function.Injective f := by
    have h2 : Function.Injective (Finsupp.linearCombination D.host.E F'.fvec) := hind'
    exact h2.comp b.repr.injective
  have hB : ((VS D).hT.comp f).compl₂ f = ((VS D).hT.comp U.subtype).compl₂ U.subtype := by
    refine LinearMap.ext_basis b b fun i j => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, hfb, Submodule.subtype_apply, hbv]
    exact (flag_gram hTT F F' i j).symm
  have hiso : ∀ x y : U, (VS D).hT (f x) (f y) = (VS D).hT x y := by
    intro x y
    have h := congrArg (fun B => B x y) hB
    simpa only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply] using h
  obtain ⟨g, hg, hgf⟩ := _root_.witt_extension_theorem D.host.E (VS D).V (VS D).hT
    (fun x y => (VS D).herm.eq x y) (fun x hx => (VS D).nondeg.1 x hx) U f hinj hiso
  have hgi : ∀ i, g (F.fvec i) = F'.fvec i := by
    intro i
    have h := hgf (b i)
    rw [hbv, hfb] at h
    exact h
  refine ⟨g, hg, fun a => ?_, ?_⟩
  · have h := hgi (Fin.castSucc a)
    simpa only [FlagG.fvec, Fin.snoc_castSucc] using h
  · have h := hgi (Fin.last _)
    simpa only [FlagG.fvec, Fin.snoc_last] using h

end Flag

theorem WittExists_holds (D : D7) (X : HidaSetting D) : Formalism.L2.SG.TermTieOf.WittExists X := by
  have hT : ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := fun u =>
    Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  choose δ hδ he hz using fun u => flag_witt (hT u) rfl (X.Fu u) (Formalism.MainNotions.S.Inh.tie_flag0 D u)
  refine ⟨{ δ := δ, isom := hδ, e_eq := fun u a => ?_, z_eq := fun u => ?_ }⟩
  · have h := he u a
    rw [X.Fu_e u] at h
    exact h
  · have h := hz u
    rw [X.flagZVector u] at h
    exact h

end Formalism.L2.SG.Pf.WittFlags
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittFlags
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem gmap_mul (a b : V ≃ₗ[K] V) (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

theorem gmap_one (L : Submodule R V) : Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L = L := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_inv_gmap (a : V ≃ₗ[K] V) (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a L) = L := by
  rw [← gmap_mul, inv_mul_cancel, gmap_one]

theorem gmap_gmap_inv (a : V ≃ₗ[K] V) (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap a⁻¹ L) = L := by
  rw [← gmap_mul, mul_inv_cancel, gmap_one]

end Gen

theorem LatIso_holds (D : D7) : Formalism.L2.SG.TermTieOf.LatIso D := by
  intro β hβ Λ
  obtain ⟨-, hloc, -, hU, hLat⟩ := Formalism.HermitianLatticesTheory.isomAct _ _ _ (VS D).hT β hβ Λ
  refine ⟨fun hΛ => ?_, hLat.2, hU.2⟩
  simp only [Formalism.HermitianLatticesTheory.genus, Set.mem_setOf_eq] at hΛ ⊢
  obtain ⟨hΛL, hΛG⟩ := hΛ
  letI := hLat.2 hΛL.toIsLattice
  refine ⟨?_, fun p hp => ?_⟩
  · refine { span_eq_top := ?_ }
    have he : ((Formalism.HermitianLatticesTheory.gmap β Λ : _) : Set _) =
        (β.toLinearMap : _ → _) '' (Λ : Set _) := by
      ext x
      simp [Formalism.HermitianLatticesTheory.gmap]
    rw [he, Submodule.span_image β.toLinearMap, hΛL.span_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr β.surjective
  obtain ⟨g, hg, hgΛ⟩ := hΛG p hp
  refine ⟨β * g, (Formalism.HermitianLatticesTheory.isom _).mul_mem hβ hg, ?_⟩
  rw [gmap_mul, hgΛ, hloc p]

end Formalism.L2.SG.Pf.WittFlags
end
end

