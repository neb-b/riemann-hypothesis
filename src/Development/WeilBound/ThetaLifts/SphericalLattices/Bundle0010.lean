module

public import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0005
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0004
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locpair
public import Development.WeilBound.ThetaLifts.SphericalLattices.SplitLoc

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.FunEvInv
section
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open Formalism.UG (IsInertAt)
open GlobalTheory.LFun.InertChart (under_eq_iff)

namespace EvInv

attribute [local instance] GlobalTheory.LocalData.complRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locChar_one {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : IsInertAt F E v w) {χ : Chr F E}
    (h1 : ∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → χ z = 1) {χv : (Ev E v)ˣ →* Circle}
    (H : IsLocChar χ v χv) : χv = 1 := MonoidHom.ext fun y => by
  have h := (under_eq_iff hw w).2 rfl
  rw [PT.locChar_eq hw h H y, MonoidHom.one_apply]
  exact h1 _ (PT.locIdele_spec hw h y).1

end EvInv

open EvInv in
theorem evInvSt : EvInvSt := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hP hWl v w hw hχ ω ρ hR m Cy hL _ l hl h0 g hg φ hφ
  have hσ := hP.base.cm
  obtain ⟨r, s, hX⟩ := hP.herm
  obtain ⟨r', s', hW⟩ := hP.skew
  obtain ⟨ψv, dv, χXv, χWv, omv, L⟩ := ThKH.Locpair.locPairEx F E σ n d B X W M om χX χW hP hWl v
  obtain rfl : χWv = 1 := locChar_one hw hχ L.chW
  obtain ⟨c1, c2⟩ := PT.psi_good hP.base.std (hP.base.inert v w hw).2.2 L.psi
  have a1 := PT.isHerm_loc (v := v) hX
  have a2 := PT.isSkew_loc (v := v) hW
  have a3 := PT.isLagr_loc hσ hw hW hL
  have a4 := PT.isEv_of L hL.supp hl h0
  have fix := split_character_fixes_evaluation _ _ _ ψv (PT.isField_Ev hw) (PT.isQuad_Ev hσ v) c1 c2 _ _ _ _ _ _ dv _ _ _ l a1 a2 a3 L.weil a4
  obtain ⟨gv, -, e1, -, -⟩ := L.loc g hg 1 (one_mem_UAt W v)
  have e : ω (g, 1) φ = omv.comp (MonoidHom.inl _ _) gv φ :=
    (PT.actsX L hg e1 hφ _).1 ((hR.acts g hg 1 (one_mem_UAt W v) φ hφ _).2 rfl)
  rw [e]
  exact fix gv φ hφ

end PositivityTheory.Sph

end
end

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.FunSieg
section
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
  PositivityTheory.ThK.PT

namespace FunSieg

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locField {F : Type} [Field F] [NumberField F] (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) :=
  GlobalTheory.LocalData.isLocalField v

local instance charZeroFv {F : Type} [Field F] [NumberField F] (v : Pl F) : CharZero (Fv F v) :=
  charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective

local instance invTwoFv {F : Type} [Field F] [NumberField F] (v : Pl F) : Invertible (2 : Fv F v) :=
  invertibleOfNonzero two_ne_zero

local instance modTopEv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) :
    IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩

theorem siegSt : SiegSt := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW P hW v w hw _ ω ρ hR m Cy hL _ l hl p hp t hpt z hz hzt u hu φ hφ
  obtain ⟨ψv, dv, χXv, χWv, omv, L⟩ := ThKH.Locpair.locPairEx F E σ n d B X W M om χX χW P hW v
  have hσ := P.base.cm
  obtain ⟨r, s, hX⟩ := P.herm
  obtain ⟨r', s', hWs⟩ := P.skew
  obtain ⟨c1, c2⟩ := psi_good P.base.std (P.base.inert v w hw).2.2 L.psi
  have a1 := isHerm_loc (v := v) hX
  have a2 := isSkew_loc (v := v) hWs
  have a3 := isLagr_loc hσ hw hWs hL
  have R := siegel_transport _ _ _ ψv (isField_Ev hw) (isQuad_Ev hσ v) c1 c2 _ _ _ _ _ _ dv _ _ _ a1 a2 a3 L.weil.1
  obtain ⟨hv, ehv⟩ := exW L hp
  have eω : ω (1, p) φ = omv.comp (MonoidHom.inr _ _) hv φ :=
    (actsW L hp ehv hφ _).1 ((hR.acts 1 (one_mem_UAt X v) p hp φ hφ (ω (1, p) φ)).2 rfl)
  by_cases h0 : ∃ φ ∈ SB (Fin n × Fin d → Fv F v), l φ ≠ 0
  · have hdet : IsUnit (t.map (compFin F E v)).det := by
      rw [← hzt]; exact (Units.map (compFin F E v).toMonoidHom z).isUnit
    let tv : GL (Fin m) (Ev E v) := ((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit
    have htv : (tv : Matrix (Fin m) (Fin m) (Ev E v)) = t.map (compFin F E v) := rfl
    have hdt : Matrix.GeneralLinearGroup.det tv = Units.map (compFin F E v).toMonoidHom z :=
      Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, htv]; exact hzt.symm)
    have hpv : ((hv : GL (Fin d) (Ev E v)) : Matrix (Fin d) (Fin d) (Ev E v)) * Cy.map (compFin F E v) =
        Cy.map (compFin F E v) * (tv : Matrix (Fin m) (Fin m) (Ev E v)) := by
      rw [show ((hv : GL (Fin d) (Ev E v)) : Matrix (Fin d) (Fin d) (Ev E v)) = hv.1.1 from rfl, ← ehv, htv,
        ← Matrix.map_mul, ← Matrix.map_mul, hpt]
    have hu' : Units.map (Algebra.norm (Fv F v) : Ev E v →* Fv F v) (Matrix.GeneralLinearGroup.det tv) = u :=
      Units.ext (by rw [hdt, hu]; rfl)
    have key := R l (Set.mem_univ _) (isEv_of L hL.supp hl h0).2 hv tv hpv φ hφ
    rw [eω, key, hu', hdt, L.chX z hz, Fintype.card_fin]
  · push Not at h0
    rw [h0 _ (hR.pres 1 (one_mem_UAt X v) p hp φ hφ), h0 φ hφ, mul_zero]

end FunSieg

theorem siegSt : SiegSt := FunSieg.siegSt

end PositivityTheory.Sph

end
end

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.SphSplitOf
section
noncomputable section

namespace PositivityTheory.Sph.SplitPl

open scoped Matrix Topology
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
  GlobalTheory.SplitFlip PositivityTheory.KCo

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

theorem intInd_eq (v : Pl F) {a b : ℕ} : (SplitDict.intInd v : Matrix (Fin a) (Fin b) (Fv F v) → ℂ) =
    Set.indicator {Z : Matrix (Fin a) (Fin b) (Fv F v) | ∀ i j, Z i j ∈ 𝒪[Fv F v]} (fun _ => (1 : ℂ)) := by
  unfold SplitDict.intInd
  congr 1
  ext Z
  exact forall₂_congr fun i j => (GlobalTheory.WeylFour.IndOSelf.mem_int_iff _).symm

theorem sphAt_of (hL : LatSt) {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
    {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {α : (Fv F v)ˣ →* ℂˣ}
    (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hs : M.vac v ∈ SB _) (hvac : ι (M.vac v) = SplitDict.intInd v)
    (hg : ∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), Reads v ι (om (g, 1)) (omB 1 α g₀ 1))
    (hh : ∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), Reads v ι (om (1, h)) (omB 1 α 1 h₀)) :
    SphAt M ψ om v := by
  intro ω ρ L
  have rg : ∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ω (g, 1) φ ∈ SB _ ∧ ι (ω (g, 1) φ) = omB 1 α g₀ 1 (ι φ) := fun g₀ => by
    obtain ⟨g, hg', r⟩ := hg g₀
    refine ⟨g, hg', fun φ hφ => ?_⟩
    obtain ⟨φ₁, h₁, ha, e⟩ := r φ hφ
    rw [(L.acts g hg' 1 (one_mem_UAt W v) φ hφ φ₁).1 ha] at h₁ e
    exact ⟨h₁, e⟩
  have rh : ∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ω (1, h) φ ∈ SB _ ∧ ι (ω (1, h) φ) = omB 1 α 1 h₀ (ι φ) := fun h₀ => by
    obtain ⟨h, hh', r⟩ := hh h₀
    refine ⟨h, hh', fun φ hφ => ?_⟩
    obtain ⟨φ₁, h₁, ha, e⟩ := r φ hφ
    rw [(L.acts 1 (one_mem_UAt X v) h hh' φ hφ φ₁).1 ha] at h₁ e
    exact ⟨h₁, e⟩
  have liftR : ∀ f ∈ Submodule.span ℂ {f | ∃ h : GL (Fin d) (Fv F v), f = fun Y =>
      Set.indicator {Z : Matrix (Fin n) (Fin d) (Fv F v) | ∀ i j, Z i j ∈ 𝒪[Fv F v]} (fun _ => (1 : ℂ)) (Y * h.1)},
      ∃ z ∈ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) (M.vac v)},
        z ∈ SB (Fin n × Fin d → Fv F v) ∧ ι z = f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h₀, rfl⟩ := hx
      obtain ⟨h, hh', r⟩ := rh h₀
      obtain ⟨hS, e⟩ := r _ hs
      have hc : (α (gdet h₀) : ℂ) * apow (gdet h₀) ((n : ℂ) / 2) ≠ 0 := mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
      refine ⟨((α (gdet h₀) : ℂ) * apow (gdet h₀) ((n : ℂ) / 2))⁻¹ • ω (1, h) (M.vac v),
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, hh', rfl⟩), Submodule.smul_mem _ _ hS, ?_⟩
      rw [map_smul, e, hvac, split_weil_rep_right_action, intInd_eq]
      funext Y
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    | zero => exact ⟨0, zero_mem _, zero_mem _, map_zero ι⟩
    | add x y _ _ hx hy =>
      obtain ⟨z, hz, hzS, e⟩ := hx
      obtain ⟨z', hz', hzS', e'⟩ := hy
      exact ⟨z + z', add_mem hz hz', add_mem hzS hzS', by rw [map_add (f := _), e, e']⟩
    | smul a x _ hx =>
      obtain ⟨z, hz, hzS, e⟩ := hx
      exact ⟨a • z, Submodule.smul_mem _ a hz, Submodule.smul_mem _ a hzS, by rw [map_smul, e]⟩
  have liftL : ∀ f ∈ Submodule.span ℂ {f | ∃ g : GL (Fin n) (Fv F v), f = fun Y =>
      Set.indicator {Z : Matrix (Fin n) (Fin d) (Fv F v) | ∀ i j, Z i j ∈ 𝒪[Fv F v]} (fun _ => (1 : ℂ)) (g.1 * Y)},
      ∃ z ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ X (evFin F v), z = ω (g, 1) (M.vac v)},
        z ∈ SB (Fin n × Fin d → Fv F v) ∧ ι z = f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, rfl⟩ := hx
      obtain ⟨g, hg', r⟩ := rg (invT g₀)⁻¹
      obtain ⟨hS, e⟩ := r _ hs
      have hc : apow (gdet (invT g₀)⁻¹) ((d : ℂ) / 2) ≠ 0 := apow_ne_zero _ _
      refine ⟨(apow (gdet (invT g₀)⁻¹) ((d : ℂ) / 2))⁻¹ • ω (g, 1) (M.vac v),
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg', rfl⟩), Submodule.smul_mem _ _ hS, ?_⟩
      rw [map_smul, e, hvac, split_weil_rep_left_action, intInd_eq, invT_inv_val, Matrix.transpose_transpose]
      funext Y
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    | zero => exact ⟨0, zero_mem _, zero_mem _, map_zero ι⟩
    | add x y _ _ hx hy =>
      obtain ⟨z, hz, hzS, e⟩ := hx
      obtain ⟨z', hz', hzS', e'⟩ := hy
      exact ⟨z + z', add_mem hz hz', add_mem hzS hzS', by rw [map_add (f := _), e, e']⟩
    | smul a x _ hx =>
      obtain ⟨z, hz, hzS, e⟩ := hx
      exact ⟨a • z, Submodule.smul_mem _ a hz, Submodule.smul_mem _ a hzS, by rw [map_smul, e]⟩
  refine ⟨M.vac v, hs, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨m, g, hgK, hinv⟩ := avgL (hb.1 hφ)
    choose x hx hxr using fun i => rg (invT (g i))
    have hterm : ∀ i, ι (ω (x i, 1) φ) = fun Y => ι φ (((g i)⁻¹).val * Y) := fun i => by
      rw [(hxr i φ hφ).2, split_weil_rep_left_action, apow_KO (invT_mem_KO (hgK i))]
      funext Y
      rw [one_mul, invT_val, Matrix.transpose_transpose]
    set φ' := ∑ i, ω (x i, 1) φ with hφ'
    have hφ'S : φ' ∈ SB _ := sum_mem fun i _ => (hxr i φ hφ).1
    have hφ'ι : ι φ' = fun Y => ∑ i, ι φ (((g i)⁻¹).val * Y) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hφ', map_sum]
      funext Y
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ => congrFun (hterm i) Y
    have hf : (fun Y => ∑ i, ι φ (((g i)⁻¹).val * Y)) ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)) := hφ'ι ▸ hb.1 hφ'S
    obtain ⟨z, hz, hzS, hzι⟩ := liftR _ (hL (Fv F v) n d _ hf fun h hh Y => hinv h hh Y)
    have hz' : z = φ' := hb.2.1 hzS hφ'S (hzι.trans hφ'ι.symm)
    have haug : ((m + 1 : ℕ) : ℂ) • φ - φ' ∈ augAt om v := by
      have e : ((m + 1 : ℕ) : ℂ) • φ - φ' = ∑ i : Fin (m + 1), -(ω (x i, 1) φ - φ) := by
        rw [hφ', Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul ℂ, neg_sub]
      rw [e]
      exact sum_mem fun i _ => neg_mem (PositivityTheory.Sph.IsLocRep.sub_mem_aug L (hx i) hφ)
    have hc : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)
    refine Submodule.mem_sup.2 ⟨_, Submodule.smul_mem _ (((m + 1 : ℕ) : ℂ)⁻¹) haug, _,
      Submodule.smul_mem _ (((m + 1 : ℕ) : ℂ)⁻¹) (hz' ▸ hz), ?_⟩
    rw [← smul_add, sub_add_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · obtain ⟨m, h, hhK, hinv⟩ := avgR (hb.1 hφ)
    choose y hy hyr using fun i => rh (h i)
    have hterm : ∀ i, ∀ ψ' ∈ SB (Fin n × Fin d → Fv F v),
        ι (((α (gdet (h i)) : ℂ))⁻¹ • ω (1, y i) ψ') = fun Y => ι ψ' (Y * (h i).val) := fun i ψ' hψ' => by
      rw [map_smul, (hyr i ψ' hψ').2, split_weil_rep_right_action, apow_KO (hhK i)]
      funext Y
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
    have hfix : ∀ i, ((α (gdet (h i)) : ℂ))⁻¹ • ω (1, y i) (M.vac v) = M.vac v := fun i =>
      hb.2.1 (Submodule.smul_mem _ _ (hyr i _ hs).1) hs (by
        rw [hterm i _ hs, hvac, intInd_eq]
        funext Y
        exact ind_mulKO Y (hhK i))
    set φ' := ∑ i, ((α (gdet (h i)) : ℂ))⁻¹ • ω (1, y i) φ with hφ'
    have hφ'S : φ' ∈ SB _ := sum_mem fun i _ => Submodule.smul_mem _ _ (hyr i φ hφ).1
    have hφ'ι : ι φ' = fun Y => ∑ i, ι φ (Y * (h i).val) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hφ', map_sum]
      funext Y
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ => congrFun (hterm i φ hφ) Y
    have hf : (fun Y => ∑ i, ι φ (Y * (h i).val)) ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)) := hφ'ι ▸ hb.1 hφ'S
    obtain ⟨z, hz, hzS, hzι⟩ := liftL _ (latT hL hf fun k hk Y => hinv k hk Y)
    have hz' : z = φ' := hb.2.1 hzS hφ'S (hzι.trans hφ'ι.symm)
    obtain ⟨c, hc⟩ := PositivityTheory.Sph.IsLocRep.span_vac L hs hz
    rw [hz', hφ'] at hc
    exact ⟨m, y, fun i => ((α (gdet (h i)) : ℂ))⁻¹, c, fun i => ⟨hy i, hfix i⟩, hc⟩

end PositivityTheory.Sph.SplitPl

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

end PositivityTheory.Sph

end
end

