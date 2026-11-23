module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.NatCastTmul
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem eps_idem {I : AutInst} {g r k : ℕ} {e f : Fin r → Fin I.n → I.E} (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) :
    PI.FinKW.psiV I v Rf.ew * PI.FinKW.psiV I v Rf.ew = PI.FinKW.psiV I v Rf.ew := by
  rw [← map_mul, Rf.ew_idem]

theorem eps_orth {I : AutInst} {g r k : ℕ} {e f : Fin r → Fin I.n → I.E} (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) :
    PI.FinKW.psiV I v Rf.ew * PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) = 0 := by
  rw [← PI.UnitaryGroupMassFormula.AdIndexEq.psiV_sigR, ← map_mul]
  have h := Rf.ew_orth
  have h' : Rf.ew * Formalism.UG.sigR I.cm.sig (Af I.F) Rf.ew = 0 := h
  rw [h', map_zero]

theorem incl_mem_Lf (I : AutInst) (l : Fin I.n → I.E) (hl : l ∈ I.L) :
    (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) ∈ I.Lf :=
  Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

theorem vecV_incl (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (l : Fin I.n → I.E) :
    PI.FinKW.vecV I v (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) =
      Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l := by
  funext i
  simp only [PI.FinKW.vecV, PI.FinKW.LocTo.psiV_inclE]
  rfl

theorem full_loc {I : AutInst} {g r k : ℕ} {e f : Fin r → Fin I.n → I.E} (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) (x : Fin I.n → RV I v)
    (hx : x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      (1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)) • x =
        (g : RV I v) • w := by
  set c := (1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)) with hc
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have hy := Rf.ew_full _ (incl_mem_Lf I l hl)
    obtain ⟨w, hw, hw'⟩ := vecV_mL I v g _ hy
    refine ⟨w, hw, ?_⟩
    rw [← hw', vecV_smul', vecV_incl, map_sub, map_sub, map_one]
    have : PI.FinKW.psiV I v (sigA I Rf.ew) = PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) :=
      PI.UnitaryGroupMassFormula.AdIndexEq.psiV_sigR I v Rf.ew
    rw [this]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w1, hw1, h1⟩ := hx
    obtain ⟨w2, hw2, h2⟩ := hy
    exact ⟨w1 + w2, Submodule.add_mem _ hw1 hw2, by rw [smul_add, h1, h2, smul_add]⟩
  | smul o x _ hx =>
    obtain ⟨w, hw, h⟩ := hx
    refine ⟨o • w, Submodule.smul_mem _ o hw, ?_⟩
    rw [PI.FinKW.LocTo.ov_smul_vec, PI.FinKW.LocTo.ov_smul_vec, smul_comm, h, smul_comm]

theorem latLoc_fg (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).FG := by
  classical
  have hL : (I.L.restrictScalars ℤ).FG := I.L_fg.restrictScalars
  obtain ⟨S, hS⟩ := hL
  have hSL : ∀ s ∈ S, s ∈ I.L := by
    intro s hs
    have : s ∈ I.L.restrictScalars ℤ := hS ▸ Submodule.subset_span hs
    exact this
  refine ⟨S.image (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)), ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    simp only [Finset.coe_image] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact Submodule.subset_span ⟨s, hSL s hs, rfl⟩
  · rw [Formalism.L2.SG.Sub.latLoc, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l ∈ Submodule.span ℤ (S : Set (Fin I.n → I.E)) := by
      rw [hS]; exact hl
    clear hl
    induction hl' using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨s, hs, rfl⟩)
    | zero =>
      have : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (0 : Fin I.n → I.E) = 0 := by
        funext i; simp [Formalism.L2.SG.Sub.ratV]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (x + y) =
          Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) x +
            Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) y := by
        funext i; simp [Formalism.L2.SG.Sub.ratV]
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (a • x) =
          a • Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) x := by
        funext i; simp [Formalism.L2.SG.Sub.ratV]
      rw [this]; exact Submodule.smul_of_tower_mem _ a hx

end PI.UnitaryGroupMassFormula.ScXuExists
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SplitUnitaryProjectionCompatibility
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB

open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

set_option maxHeartbeats 1000000 in
theorem split_unitary_projection_compatibility : BridgeB := by
  intro I g r k e f z Rf _hH v _hv _hsum p1 hp1 T hT
  have hε : ∀ w ∈ LL I v, PI.FinKW.psiV I v Rf.ew • w ∈ LL I v := fun w hw =>
    PI.FinKW.LocTo.intAf_le_mulSet I v Rf.ew_int w hw
  have : Module.Finite I.F I.E := Module.finite_of_finrank_eq_succ I.cm.deg2
  have hdim : Module.finrank (KV I v) (RV I v) = 2 := by
    rw [Module.finrank_baseChange]; exact I.cm.deg2
  have hb := piHom_bijective hdim (sigV I v) p1 (sigV_alg I v) (sigV_sigV I v) hp1.1
    (PI.FinKW.psiV I v Rf.ew) hp1.2.1 hp1.2.2.1
  set π := piEquiv (sigV I v) p1 hb with hπdef
  have hπ : ∀ r, π (sigV I v r) = (π r).swap := piEquiv_sig _ _ (sigV_sigV I v) hb
  have hchar := mem_LL_iff I v _ p1 hp1 hb.1 hε
  obtain ⟨y, hy⟩ := (SplitGL.proj_bijective (sigV I v) π hπ _ (spl_herm_v I v) (spl_det_v I v)).2 T
  subst hy
  have hPm : (I.J.map (inclV I v)).map (SplitGL.p1 π) = Pm I v p1 := by ext i j; rfl

  have v1 : ∀ (y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) (X : Fin I.n → RV I v),
      vec1 p1 (((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X) =
        ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y' : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v)) *ᵥ
          vec1 p1 X := by
    intro y' X; funext i; exact RingHom.map_mulVec p1 _ _ i
  have v2 : ∀ (y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) (X : Fin I.n → RV I v),
      vec2 p1 (((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X) =
        ((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)).map (SplitGL.p2 π) *ᵥ
          vec2 p1 X := by
    intro y' X; funext i; exact RingHom.map_mulVec (p1.comp (sigV I v)) _ _ i
  have vp2 : ∀ (y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) (β β' : Fin I.n → KV I v),
      β' ᵥ* Pm I v p1 = (β ᵥ* Pm I v p1) ᵥ*
        (((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y')⁻¹ : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v)) →
      ((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)).map (SplitGL.p2 π) *ᵥ β = β' := by
    intro y' β β' h
    rw [← hPm] at h
    exact second_projection_mulVec_eq (sigV I v) π hπ _ (spl_det_v I v) y' β β' h
  have extv : ∀ X X' : Fin I.n → RV I v, vec1 p1 X = vec1 p1 X' → vec2 p1 X = vec2 p1 X' → X = X' := by
    intro X X' h1 h2
    funext i
    apply hb.1
    exact Prod.ext (congrFun h1 i) (congrFun h2 i)

  have fwd : ∀ y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v)),
      (∀ x ∈ Lam1 I v p1, ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y' : GL (Fin I.n) (KV I v)) :
        Matrix (Fin I.n) (Fin I.n) (KV I v)) *ᵥ x ∈ Lam1 I v p1) →
      (∀ β ∈ Lam2 I v p1, ∃ β' ∈ Lam2 I v p1, β' ᵥ* Pm I v p1 = (β ᵥ* Pm I v p1) ᵥ*
        (((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y')⁻¹ : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v))) →
      ∀ w ∈ LL I v, ((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ w ∈ LL I v := by
    intro y' h1 h2 w hw
    rw [hchar] at hw ⊢
    obtain ⟨hw1, hw2⟩ := hw
    refine ⟨?_, ?_⟩
    · rw [v1]; exact h1 _ hw1
    · rw [v2]
      obtain ⟨β', hβ', eβ⟩ := h2 _ hw2
      rw [vp2 y' _ β' eβ]
      exact hβ'
  have hinvproj : SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y⁻¹ = (SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y)⁻¹ := map_inv _ y
  have fwdY := fwd y (fun x hx => (hT.1 x hx).1) (fun β hβ => (hT.2.1 β hβ).2)
  have fwdYi := fwd y⁻¹ (fun x hx => by rw [hinvproj]; exact (hT.1 x hx).2)
    (fun β hβ => by rw [hinvproj, inv_inv]; exact (hT.2.1 β hβ).1)
  have hYiY : ∀ X : Fin I.n → RV I v,
      (((y⁻¹ : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) : GL (Fin I.n) (RV I v)) :
        Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ
        (((y : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X) = X := by
    intro X
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]
    have : ((y⁻¹ : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) : GL (Fin I.n) (RV I v)) *
        (y : GL (Fin I.n) (RV I v)) = 1 := by
      rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
    rw [this, Units.val_one, Matrix.one_mulVec]
  have fixv : ∀ X : Fin I.n → RV I v,
      ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v)) *ᵥ
        vec1 p1 X = vec1 p1 X →
      (vec2 p1 X ᵥ* Pm I v p1) ᵥ* ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y : GL (Fin I.n) (KV I v)) :
        Matrix (Fin I.n) (Fin I.n) (KV I v)) = vec2 p1 X ᵥ* Pm I v p1 →
      ((y : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X = X := by
    intro X h1 h2
    apply extv
    · rw [v1, h1]
    · rw [v2]
      apply vp2
      symm
      calc (vec2 p1 X ᵥ* Pm I v p1) ᵥ*
            (((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y)⁻¹ : GL (Fin I.n) (KV I v)) :
              Matrix (Fin I.n) (Fin I.n) (KV I v))
          = ((vec2 p1 X ᵥ* Pm I v p1) ᵥ* ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y :
              GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v))) ᵥ*
            (((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y)⁻¹ : GL (Fin I.n) (KV I v)) :
              Matrix (Fin I.n) (Fin I.n) (KV I v)) := by rw [h2]
        _ = vec2 p1 X ᵥ* Pm I v p1 := by
          rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  refine ⟨(y : GL (Fin I.n) (RV I v)), y.2, ?_, ?_, ?_⟩
  ·
    intro x
    refine ⟨fun hx => fwdY x hx, fun hx => ?_⟩
    have := fwdYi _ hx
    rwa [hYiY] at this
  ·
    intro a
    obtain ⟨h1, h2, h3, h4⟩ := hT.2.2.1 a
    exact ⟨fixv _ h1 h3, fixv _ h2 h4⟩
  ·
    obtain ⟨w1, hw1, hw1e⟩ := hT.2.2.2.1
    obtain ⟨β, hβ, hβe⟩ := hT.2.2.2.2
    set w : Fin I.n → RV I v := fun i => π.symm (w1 i, β i) with hwdef
    have hw1' : vec1 p1 w = w1 := by
      funext i
      show SplitGL.p1 π (π.symm (w1 i, β i)) = w1 i
      simp [SplitGL.p1]
    have hw2' : vec2 p1 w = β := by
      funext i
      show SplitGL.p2 π (π.symm (w1 i, β i)) = β i
      simp [SplitGL.p2]
    have hwL : w ∈ LL I v := (hchar w).2 ⟨hw1' ▸ hw1, hw2' ▸ hβ⟩
    refine ⟨w, hwL, ?_⟩
    have hyi : ((y : GL (Fin I.n) (RV I v))⁻¹ : GL (Fin I.n) (RV I v)) =
        ((y⁻¹ : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) : GL (Fin I.n) (RV I v)) := rfl
    rw [hyi]
    apply extv
    · rw [first_coordinate_vector_sub, v1, first_coordinate_vector_nsmul, hw1', hinvproj]
      exact hw1e
    · rw [second_coordinate_vector_sub, v2, second_coordinate_vector_nsmul, hw2']
      rw [vp2 y⁻¹ _ (vec2 p1 (PI.FinKW.vecV I v Rf.z0) + (g : KV I v) • β)]
      · abel
      · rw [hinvproj, inv_inv, Matrix.add_vecMul, Matrix.smul_vecMul, ← hβe]
        abel

end PI.UnitaryGroupMassFormula.ScXuExists.BrB
end
end

