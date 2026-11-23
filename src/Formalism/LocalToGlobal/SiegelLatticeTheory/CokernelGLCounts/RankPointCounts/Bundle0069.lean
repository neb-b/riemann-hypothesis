module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0064
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0058
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmLocPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0055
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0065
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarNMove
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaRat
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated
  Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open BwdCut BwdBetaCut OmP BwdBetaS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)


set_option maxHeartbeats 1000000 in
theorem betaRat_holds : BetaRat Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB
  obtain ⟨hC, hCtx, hS, -, -, hTH, hPD, hGv⟩ := hB
  obtain ⟨hZd, hZ₁d', hx'⟩ := starMinors_holds u u' F0 what₂ γ Z hCtx
  have hZ : ZhatL (lf D F0) F'₂ = Z := hS.1
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hΛ : Submodule.IsFullLattice D.host.E γ.lam := hrow.1.1
  have hLlf : IsLift γ.lam (lf D F0) := hrow.2.1.2.2.1
  have hLrep : IsLift γ.lam (repF γ) := hPD.1
  set f := frame (lf D F0) with hf
  set g := frame (repF γ) with hg
  set F₂ := F'₂.fl with hF₂
  set Z₁ := starZh f g with hZ₁
  have hlm : ∀ l, leadMinorE Z₁ l = leadMinorE (starZh f (starFrame γ)) l := fun l => (star_frame_lead_minor γ l).symm
  have hZ₁d : Z₁.det ≠ 0 := by
    rw [← FsLA.leadMinorE_full, hlm, FsLA.leadMinorE_full]; exact hZ₁d'
  have hx : leadMinorE Z₁ D.R.rS * Z.det = leadMinorE Z D.R.rS * Z₁.det := by
    rw [hlm, ← FsLA.leadMinorE_full Z₁, hlm, FsLA.leadMinorE_full]; exact hx'
  have hfF : f = F0.fvec := rfl
  have hZe : ∀ a b, (VS D).hT (f a) (F₂.fvec b) = Z a b := fun a b => by rw [← hZ]; rfl
  have hg2 : FsLA.gram (VS D) f F₂.fvec = Zᴴ := by
    refine Matrix.ext fun i j => ?_
    simp only [FsLA.gram, Matrix.conjTranspose_apply]
    rw [← hZe, ← (LinearMap.isSymm_def.1 (VS D).herm) (f j) (F₂.fvec i), starRingEnd_apply]
  have h1g : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (g a) (g b) = 0 :=
    fun a b h => FsLA.gram_fvec_zero (repF γ).fl a b h
  have h2g : (VS D).hT (g (Fin.last D.R.rS)) (g (Fin.last D.R.rS)) = -((Tu D u' : ℕ) : D.host.E) :=
    FsLA.gram_fvec_last (repF γ).fl
  have h1f : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (f a) (f b) = 0 :=
    fun a b h => FsLA.gram_fvec_zero F0 a b h
  have h2f : (VS D).hT (f (Fin.last D.R.rS)) (f (Fin.last D.R.rS)) = -CntLocal.Tn u := FsLA.gram_fvec_last F0
  have hdZ1h : Z₁ᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hZ₁d
  have hdg2 : (FsLA.gram (VS D) f F₂.fvec).det ≠ 0 := by
    rw [hg2, Matrix.det_conjTranspose]; exact star_ne_zero.2 hZd
  have hx2 : leadMinorE (FsLA.gram (VS D) f F₂.fvec) D.R.rS * Z₁ᴴ.det =
      leadMinorE Z₁ᴴ D.R.rS * (FsLA.gram (VS D) f F₂.fvec).det := by
    rw [hg2, FsLA.lm_conjTranspose, FsLA.lm_conjTranspose, Matrix.det_conjTranspose, Matrix.det_conjTranspose,
      ← star_mul', ← star_mul', mul_comm (leadMinorE Z D.R.rS), hx, mul_comm]
  obtain ⟨F₃, hZ3, hom3, hsp3⟩ := FsLA.frame_la F₂ f h1f h2f Z₁ᴴ hdZ1h hdg2 hx2
  set h := F₃.fvec with hh
  set uu := Sum.elim f g with huu
  set uu' := Sum.elim h F₂.fvec with huu'
  set ww := Sum.elim f F₂.fvec with hww
  have hZ3e : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = Z₁ᴴ a b := fun a b => congrFun (congrFun hZ3 a) b
  have k1 : ∀ a b, (VS D).hT (h a) (h b) = (VS D).hT (f a) (f b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₃ a b hab).trans (FsLA.gram_fvec_zero F0 a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₃).trans (FsLA.gram_fvec_last F0).symm
  have k2 : ∀ a b, (VS D).hT (h a) (F₂.fvec b) = (VS D).hT (f a) (g b) := by
    intro a b
    rw [← (LinearMap.isSymm_def.1 (VS D).herm) (F₂.fvec b) (h a), hZ3e, starRingEnd_apply,
      Matrix.conjTranspose_apply, star_star]
    rfl
  have k3 : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = (VS D).hT (g a) (f b) := by
    intro a b
    rw [hZ3e, Matrix.conjTranspose_apply, ← starRingEnd_apply]
    exact (LinearMap.isSymm_def.1 (VS D).herm) (f b) (g a)
  have k4 : ∀ a b, (VS D).hT (F₂.fvec a) (F₂.fvec b) = (VS D).hT (g a) (g b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₂ a b hab).trans (h1g a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₂).trans h2g.symm
  have hGr : FsLA.gram (VS D) uu' uu' = FsLA.gram (VS D) uu uu := by
    refine Matrix.ext fun i j => ?_
    rcases i with a | a <;> rcases j with b | b
    · exact k1 a b
    · exact k2 a b
    · exact k3 a b
    · exact k4 a b
  have hGg : (FsLA.gram (VS D) g F0.fvec).det * star (FsLA.gram (VS D) g F0.fvec).det -
      CntLocal.Tn u * ((Tu D u' : ℕ) : D.host.E) *
        (leadMinorE (FsLA.gram (VS D) g F0.fvec) D.R.rS * star (leadMinorE (FsLA.gram (VS D) g F0.fvec) D.R.rS))
        ≠ 0 := by
    rw [← FsLA.leadMinorE_full]; exact hGv
  have hdet : (FsLA.gram (VS D) uu uu).det ≠ 0 := FsLA.gram_pair_det F0 g h1g h2g hZ₁d hGg
  have hGZ : Gflag F0 F₂ ≠ 0 := hTH.1.2.2
  have hGg₂ : (FsLA.gram (VS D) F₂.fvec F0.fvec).det * star (FsLA.gram (VS D) F₂.fvec F0.fvec).det -
      CntLocal.Tn u * ((Tu D u' : ℕ) : D.host.E) *
        (leadMinorE (FsLA.gram (VS D) F₂.fvec F0.fvec) D.R.rS *
          star (leadMinorE (FsLA.gram (VS D) F₂.fvec F0.fvec) D.R.rS)) ≠ 0 := by
    rw [← FsLA.leadMinorE_full]; exact hGZ
  have hdetZ : (Zhat F0 F₂).det ≠ 0 := by
    have e : Zhat F0 F₂ = Z := hZ
    rw [e]; exact hZd
  have hdetw : (FsLA.gram (VS D) ww ww).det ≠ 0 :=
    FsLA.gram_pair_det F0 F₂.fvec (fun a b hab => FsLA.gram_fvec_zero F₂ a b hab) (FsLA.gram_fvec_last F₂)
      hdetZ hGg₂
  have hsp : ∀ i, uu' i ∈ Submodule.span D.host.E (Set.range ww) := by
    have hsub : Set.range (Sum.elim F₂.fvec f) ⊆ Submodule.span D.host.E (Set.range ww) := by
      rintro _ ⟨k, rfl⟩
      rcases k with b | a
      · exact Submodule.subset_span ⟨Sum.inr b, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    intro i
    rcases i with a | b
    · exact Submodule.span_le.2 hsub (hsp3 a)
    · exact Submodule.subset_span ⟨Sum.inr b, rfl⟩

  have hdetγ : (Zhat F0 (repF γ).fl).det ≠ 0 := hZ₁d
  obtain ⟨Ω₂, hΩ₂⟩ := exists_om F0 F₂ hdetZ
  obtain ⟨Ωγ, hΩγ⟩ := exists_om F0 (repF γ).fl hdetγ
  have hΩd : Ω₂ - Ωγ ∈ Xsp (lf D F0) :=
    omega_local_holds Zd u u' F0 what₂ hC.2.1 γ Z hCtx F'₂ φ φ' hS hdetγ hZd Ω₂ Ωγ hΩ₂ hΩγ

  have hXq : ∀ y, (∀ k, (VS D).hT (uu k) y = 0) → FsLA.lin ww (FsLA.pc ww y) ∈ F0.X := by
    intro y hy
    have hrem := fun z hz => (FsLA.hT_span_rem ww hdetw y z hz).1
    have hyU : ∀ z ∈ Submodule.span D.host.E (Set.range uu), (VS D).hT z y = 0 :=
      NMoveP.spanL (VS D) uu y hy
    refine BRat.key_X F0 F₂ hdetZ hΩ₂ hGZ (FsLA.lin_sub ww _) (fun a => ?_) ?_
    · have e := hrem (f a) (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
      rw [map_sub, sub_eq_zero] at e
      rw [← e]
      exact hy (Sum.inl a)
    · have e := hrem Ω₂ (Submodule.span_mono (Set.range_comp_subset_range Sum.inr ww) hΩ₂.1)
      rw [map_sub, sub_eq_zero] at e
      rw [← e]
      have e2 : Ω₂ = Ωγ + (Ω₂ - Ωγ) := by abel
      rw [e2, map_add (f := _), LinearMap.add_apply]
      have h1 : (VS D).hT Ωγ y = 0 :=
        hyU _ (Submodule.span_mono (Set.range_comp_subset_range Sum.inr uu) hΩγ.1)
      have hXu : ∀ x ∈ Xsp (lf D F0), x ∈ Submodule.span D.host.E (Set.range uu) := by
        intro x hx
        refine Submodule.span_le.2 ?_ hx
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨Sum.inl i.castSucc, by simp [huu, hf, frame, FlagG.fvec]⟩
      rw [h1, hyU _ (hXu _ hΩd), add_zero]
  have hkey : ∀ y y', (∀ k, (VS D).hT (uu k) y = 0) → (∀ k, (VS D).hT (uu k) y' = 0) →
      (VS D).hT (FsLA.lin ww (FsLA.pc ww y)) (FsLA.lin ww (FsLA.pc ww y')) = 0 :=
    fun y y' hy hy' => NMoveP.hT_X_X F0 (hXq y hy) (hXq y' hy')
  obtain ⟨β, hiso, hβu, hβy⟩ := BRat.isometry_extension_two uu uu' ww hGr hdet hdetw hsp hkey
  refine ⟨β, hiso, fun b => hβu (Sum.inr b), fun w0 hw0 => ?_, ?_⟩
  ·
    have hw0u : ∀ k, (VS D).hT (uu k) w0 = 0 := fun k =>
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw0 _
        (PI.PairCorankPos.W.frame_mem_UUE γ.lam hΛ (lf D F0) (repF γ) hLlf hLrep k)
    refine ⟨β w0, ?_, ?_, by rw [sub_self]; exact zero_mem _⟩
    · refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_
      have hxw : x ∈ Submodule.span D.host.E (Set.range ww) :=
        UUE_le_span Λ₂ (lf D F0) (liftF F'₂) rfl rfl hx
      rw [hβy w0 hw0u]
      exact (FsLA.hT_span_rem ww hdetw w0 x hxw).1
    · rw [hβy w0 hw0u, sub_sub_cancel]
      exact hXq w0 hw0u
  ·
    have homf : FsLA.om (VS D) F₂.fvec f = starOmL f (frame F'₂) := by
      rw [FsLA.om, hg2, ← Matrix.adjugate_conjTranspose]
      simp only [starOmL, Matrix.conjTranspose_apply]
      rw [← hZ]
      rfl
    have homh : FsLA.om (VS D) F₂.fvec h = β (starOmL f g) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [FsLA.om, starOmL, map_sum, map_smul]
      have e : FsLA.gram (VS D) h F₂.fvec = Z₁ᴴ := hZ3
      rw [e]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply]
      congr 1
      exact (hβu (Sum.inl a)).symm
    have e1 : Z₁ᴴ.det = star Z₁.det := Matrix.det_conjTranspose _
    have e2 : (FsLA.gram (VS D) f F₂.fvec).det = star Z.det := by rw [hg2, Matrix.det_conjTranspose]
    rw [e1, e2, homf, homh] at hom3
    have hD1 : GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1) = Z₁.det := by rw [GDl_top']; rfl
    have hD2 : GDl (frame (lf D F0)) (frame (liftF F'₂)) (D.R.rS + 1) = Z.det := by
      rw [GDl_top']; rw [← hZ]; rfl
    have hO1 : Gom (frame (lf D F0)) (frame (repF γ)) = starOmL f g := rfl
    have hO2 : Gom (frame (lf D F0)) (frame (liftF F'₂)) = starOmL f (frame F'₂) := rfl
    unfold OmB
    rw [hD1, hD2, hO1, hO2]
    have := (Xsp (liftF F'₂)).neg_mem hom3
    rw [neg_sub] at this
    exact this

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdN
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem bwdN_zorth : F0.z ∈ orth (VS D) (Xsp (lf D F0)) :=
  (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
    rw [BwdNA.hsw (VS D) F0.z x]
    have h := NMoveP.hT_f_X F0 (Fin.last D.R.rS) hx
    rw [NMoveP.fvecL] at h
    rw [h, star_zero]

theorem bwdN_znotX : F0.z ∉ Xsp (lf D F0) := by
  intro h
  have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 (bwdN_zorth (F0 := F0)) F0.z h
  rw [F0.z_norm, neg_eq_zero] at h0
  have hT := (D.mem u).A.T_prime.ne_zero
  exact hT (Nat.cast_eq_zero.1 h0)

variable (u u' F0 what₂)

set_option maxHeartbeats 1000000 in
theorem bwdN_holds : BwdN Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hmem₂
  obtain ⟨hΛ₂, hloc₂⟩ := hmem₂
  obtain ⟨-, hT2, hφ⟩ := hS
  have hrow := hC.2.1.1 γ.lam γ.mem
  have : Submodule.IsFullLattice D.host.E γ.lam := hrow.1.1
  have ht1 := fun p => (hT2 p).1
  have hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) := fun p a =>
    BwdNP.unit_of_frame Zd p γ (ht1 p).1.2.1 a
  have hSDl : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p γ.lam) := fun p => (ht1 p).1.1
  have hSDl₂ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₂) := fun p => (hloc₂ p).1.1.1
  have hpr : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f := fun p => (ht1 p).1.2.1.1
  have hpr₂ : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => (hloc₂ p).1.1.2.1.1
  have hLset : ∀ p, (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f =
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => by
    have h := (hloc₂ p).2.1
    rw [hφ p] at h
    rw [← h]
    exact (Set.image_id _).symm
  have hSD := BwdNP.sd_of_loc Zd (Λ := γ.lam) inferInstance hSDl
  have hSD₂ := BwdNP.sd_of_loc Zd (Λ := Λ₂) inferInstance hSDl₂
  set X := Xsp (lf D F0) with hXdef
  have hXiso : ∀ x ∈ X, ∀ y ∈ X, (VS D).hT x y = 0 := fun x hx y hy => NMoveP.hT_X_X F0 hx hy
  have hXX : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) X) → w ∈ X := fun {w} hw =>
    BwdNA.mem_of_orth_orth (VS D) X fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXo := BwdNA.X_le_orth (VS D) X hXiso
  have hL : ∀ x ∈ Λ₂, x ∈ orth (VS D) X → ∃ y ∈ γ.lam, y - x ∈ X := fun x hx hxo => by
    obtain ⟨w, hw, hxw⟩ := BwdNA.dual_sum (VS D) γ.lam inferInstance hSD (orth (VS D) X) x
      (fun m hmΛ hmU => BwdNP.pair_int Zd γ hSDl (fun p => (hLset p).symm.subset) hx hxo hmΛ hmU)
    refine ⟨w, hw, ?_⟩
    have h2 := X.neg_mem (hXX hxw)
    rwa [neg_sub] at h2
  have hL' : ∀ y ∈ γ.lam, y ∈ orth (VS D) X → ∃ x ∈ Λ₂, x ∈ orth (VS D) X ∧ y - x ∈ X := fun y hy hyo => by
    obtain ⟨w, hw, hyw⟩ := BwdNA.dual_sum (VS D) Λ₂ inferInstance hSD₂ (orth (VS D) X) y
      (fun m hmΛ hmU => BwdNP.pair_int Zd γ hSDl₂ (fun p => (hLset p).subset) hy hyo hmΛ hmU)
    have hX1 := hXX hyw
    refine ⟨w, hw, ?_, hX1⟩
    have e : w = y - (y - w) := by abel
    rw [e]
    exact (orth (VS D) X).sub_mem hyo (hXo hX1)
  have hXm : ∀ x ∈ X, x ∈ Λ₂ ↔ x ∈ γ.lam := fun x hx =>
    ⟨BwdNP.memX Zd γ hpr₂ hpr inferInstance hu hx, BwdNP.memX Zd γ hpr hpr₂ inferInstance hu hx⟩
  have hy := BwdNP.exists_y Zd γ (Λ₂ := Λ₂) inferInstance hSD₂ hpr₂ hu bwdN_znotX
  have htr : ∃ c : D.host.E, IsIntegral ℤ c ∧ c + star c = 1 := by
    obtain ⟨c, hc⟩ := D.host.exists_trace_one
    refine ⟨(c : D.host.E), RingOfIntegers.isIntegral_coe c, ?_⟩
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host)]
    exact hc
  obtain ⟨n, hiso, hnX, hnz, hno, himg⟩ := BwdNA.main (VS D) X hXiso F0.z bwdN_zorth γ.lam Λ₂
    inferInstance inferInstance hSD hSD₂ hXm
    (BwdNP.z_mem Zd γ (Λ := γ.lam) inferInstance hpr) (BwdNP.z_mem Zd γ (Λ := Λ₂) inferInstance hpr₂) hL hL' hy htr
  refine ⟨n, ⟨hiso, fun j x hx => ?_, hno, fun a => hnX _ (Submodule.subset_span ⟨a, rfl⟩), hnz⟩, himg⟩
  have hxX : x ∈ X := Submodule.span_mono (Set.image_subset_range _ _) hx
  rw [hnX x hxX, sub_self]
  exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfG
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching ValuativeRel

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

namespace CohGoodPf

variable {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}

def wG (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) {T' : D.host.E} (F'₂ : LFlag (D.sp.Y 0) D.R.rS T') :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V :=
  Sum.elim (frame (lf D F0)) (frame F'₂)

def gramG (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) {T' : D.host.E} (F'₂ : LFlag (D.sp.Y 0) D.R.rS T') :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) D.host.E :=
  Matrix.of fun i j => brS (VS D) (wG F0 F'₂ j) (wG F0 F'₂ i)

variable (Zd : LocDat D) (p : PlF D)

def sK : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (D.s.atP p).Ep :=
  Sum.elim (fun a => sgnP D p a * frFac Zd.δ p a) (fun b => sgnP' D p b * frFac Zd.δ p b)

def sI : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (D.s.atP p).Ep :=
  Sum.elim (fun a => sgnP D p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val))
    (fun b => sgnP' D p b * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - b.val))

theorem frFac_mul (a : Fin (D.R.rS + 1)) :
    frFac Zd.δ p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val) = 1 := by
  unfold frFac
  exact Ring.inverse_mul_cancel _ ((Formalism.L2.SG.Pf.BBTie.bt_T_unit Zd p).pow _)

theorem sI_mul (k : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) : sI Zd p k * sK Zd p k = 1 := by
  cases k with
  | inl a =>
    show sgnP D p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val) * (sgnP D p a * frFac Zd.δ p a) = 1
    calc _ = (sgnP D p a * sgnP D p a) * (frFac Zd.δ p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val)) := by ring
      _ = 1 := by rw [localSign_sq, frFac_mul, one_mul]
  | inr b =>
    show sgnP' D p b * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - b.val) * (sgnP' D p b * frFac Zd.δ p b) = 1
    calc _ = (sgnP' D p b * sgnP' D p b) * (frFac Zd.δ p b * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - b.val)) := by ring
      _ = 1 := by rw [sgnP'_sq, frFac_mul, one_mul]

variable {Zd p}

theorem split_none (hs : (Zd.M p).split = none) : (D.s.atP p).split = none := by
  have hA := (Zd.agree p).2.2.2.2.2
  rw [hs] at hA
  cases h2 : (D.s.atP p).split with
  | none => rfl
  | some sg =>
    rw [h2] at hA
    exact (hA : False).elim

theorem sI_mem (hs : (Zd.M p).split = none) (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O) (k : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) :
    sI Zd p k ∈ (D.s.atP p).O := by
  have hs' := split_none hs
  have hT : Formalism.L2.SG.Pf.BBTie.btT Zd p ∈ (D.s.atP p).O :=
    Subring.mul_mem _ (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O (D.s.atP p) hδ) hu
  cases k with
  | inl a =>
    refine Subring.mul_mem _ ?_ (Subring.pow_mem _ hT _)
    show sgnP D p a ∈ _
    unfold TermLoc.sgnP
    rw [hs']
    exact Subring.one_mem _
  | inr b =>
    refine Subring.mul_mem _ ?_ (Subring.pow_mem _ hT _)
    show sgnP' D p b ∈ _
    unfold TermLoc.sgnP'
    rw [hs']
    exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _

theorem cj_mem (y : (D.s.atP p).Ep) (hy : y ∈ (D.s.atP p).O) : (D.s.atP p).cj y ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def] at hy ⊢
  exact hy.map (((D.s.atP p).cj : (D.s.atP p).Ep →ₐ[(D.s.atP p).Fp] (D.s.atP p).Ep).restrictScalars
    𝒪[(D.s.atP p).Fp])

variable {u' : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem vP_eq' (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hs : (Zd.M p).split = none) : vP Zd p γ F'₂ = fun k => sK Zd p k • baseChange₂ D p (wG F0 F'₂ k) := by
  rw [vP_eq Zd γ F'₂ hs]
  funext k
  cases k <;> rfl

theorem gram_vP (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hs : (Zd.M p).split = none) :
    (locH Zd p).gram (vP Zd p γ F'₂) = Matrix.diagonal (fun k => (Zd.M p).L.cj (sK Zd p k)) *
      (gramG F0 F'₂).map (D.s.atP p).ιE * Matrix.diagonal (sK Zd p) := by
  rw [vP_eq' γ F'₂ hs]
  ext i j
  simp only [Formalism.MainNotions.S.Loc.HermSp.gram, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply,
    gramG]
  rw [Formalism.L2.SG.Pf.ScalarFramePf.h_bcP]
  ring

theorem gramInv_at (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hdet : (gramG F0 F'₂).det ≠ 0) (hs : (Zd.M p).split = none) (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O)
    (hent : ∀ i j, (D.s.atP p).ιE ((gramG F0 F'₂)⁻¹ i j) ∈ (D.s.atP p).O) :
    Formalism.MainNotions.S.Loc.HermSp.CohU.GramInv (locH Zd p) (vP Zd p γ F'₂) := by
  have hO : (Zd.M p).L.O = (D.s.atP p).O := Formalism.L2.SG.Pf.LocalDenominators.hO Zd p
  have hcj : (Zd.M p).L.cj = (D.s.atP p).cj := Zd.hcj p
  set M := gramG F0 F'₂ with hMdef
  set ι := (D.s.atP p).ιE with hι
  refine ⟨Matrix.diagonal (sI Zd p) * M⁻¹.map ι * Matrix.diagonal (fun k => (Zd.M p).L.cj (sI Zd p k)),
    fun i j => ?_, ?_⟩
  · simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply]
    rw [hO, hcj]
    exact Subring.mul_mem _ (Subring.mul_mem _ (sI_mem hs hδ hu i) (hent i j)) (cj_mem _ (sI_mem hs hδ hu j))
  · rw [gram_vP γ F'₂ hs]
    have hM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
    have hmap : M⁻¹.map ι * M.map ι = 1 := by
      rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero ι) (map_one ι)]
    have hc1 : (fun k => (Zd.M p).L.cj (sI Zd p k) * (Zd.M p).L.cj (sK Zd p k)) = fun _ => 1 := by
      funext k; rw [← map_mul, sI_mul, map_one]
    have hs1 : (fun k => sI Zd p k * sK Zd p k) = fun _ => 1 := funext fun k => sI_mul Zd p k
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal fun k => (Zd.M p).L.cj (sI Zd p k)), Matrix.diagonal_mul_diagonal, hc1,
      Matrix.diagonal_one, Matrix.one_mul, ← Matrix.mul_assoc (M⁻¹.map ι), hmap, Matrix.one_mul,
      Matrix.diagonal_mul_diagonal, hs1, Matrix.diagonal_one]

end CohGoodPf

open CohGoodPf

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}


variable (u u' F0 what₂) in
def GlobGramNe : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)),
    Ctx γ Z → ZhatL (lf D F0) F'₂ = Z → (gramG F0 F'₂).det ≠ 0

theorem cohGood_of (hGG : GlobGramNe u u' F0 what₂) : CohGood Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' hH
  have hdet := hGG hP γ Z F'₂ hH.1 hH.2.1
  set X : Finset D.host.E := Finset.univ.image (fun ij : (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) ×
    (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) => (gramG F0 F'₂)⁻¹ ij.1 ij.2) with hX
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite Zd.δ Zd.M Zd.agree X
  rw [Filter.eventually_cofinite] at hgood
  refine hgood.subset fun p hp => ?_
  by_contra hn
  simp only [Set.mem_ofPred_eq, not_not] at hn
  apply hp
  obtain ⟨hs, hδ, hu, hXm⟩ := hn
  refine gramInv_at γ F'₂ hdet hs hδ.1 hu.1 fun i j => ?_
  by_cases h0 : (gramG F0 F'₂)⁻¹ i j = 0
  · rw [h0, map_zero]; exact Subring.zero_mem _
  · have hmem : (gramG F0 F'₂)⁻¹ i j ∈ X := Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩
    have h := (hXm _ hmem 0 (by simpa using h0)).1
    simpa using h

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

