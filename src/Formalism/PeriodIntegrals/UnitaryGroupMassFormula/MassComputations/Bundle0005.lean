module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MeasurePrjFPreimage
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolS

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.FmatInvMul
section
noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MassDataMassesW.NLev

section Grp

variable {I : AutInst}

theorem Kset_Lf {x : I.Gf} (hx : x ∈ I.Kset) : ∀ v ∈ I.Lf, I.fmat x *ᵥ v ∈ I.Lf := by
  intro v hv
  have h : ∀ w, w ∈ I.Lf ↔ I.fmat x *ᵥ w ∈ I.Lf := hx
  exact (h v).1 hv

theorem Kset_inv {x : I.Gf} (hx : x ∈ I.Kset) : x⁻¹ ∈ I.Kset := by
  show ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [InvMemClass.coe_inv]
  exact (Formalism.UG.stabGL I.Lf).inv_mem hx

theorem Kset_mul {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) : x * y ∈ I.Kset := by
  show ((x * y : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [MulMemClass.coe_mul]
  exact (Formalism.UG.stabGL I.Lf).mul_mem hx hy

theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp only [Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv, Units.inv_mul]

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp only [Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv, Units.mul_inv]

def Tm (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v : VA I) : VA I :=
  Ai *ᵥ ((By - 1) *ᵥ (A *ᵥ v))

theorem Tm_add (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v w : VA I) :
    Tm Ai By A (v + w) = Tm Ai By A v + Tm Ai By A w := by
  simp only [Tm, Matrix.mulVec_add]

theorem Tm_sub (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v w : VA I) :
    Tm Ai By A (v - w) = Tm Ai By A v - Tm Ai By A w := by
  simp only [Tm, Matrix.mulVec_sub]

theorem Tm_smul (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (r : I.E ⊗[I.F] Af I.F) (v : VA I) :
    Tm Ai By A (r • v) = r • Tm Ai By A v := by
  simp only [Tm, Matrix.mulVec_smul]

theorem sub_one_Lf {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hM : ∀ v ∈ I.Lf, M *ᵥ v ∈ I.Lf) :
    ∀ v ∈ I.Lf, (M - 1) *ᵥ v ∈ I.Lf := by
  intro v hv
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact I.Lf.sub_mem (hM v hv) hv

theorem Tm_Lf {Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hAi : ∀ v ∈ I.Lf, Ai *ᵥ v ∈ I.Lf)
    (hBy : ∀ v ∈ I.Lf, By *ᵥ v ∈ I.Lf) (hA : ∀ v ∈ I.Lf, A *ᵥ v ∈ I.Lf) :
    ∀ v ∈ I.Lf, Tm Ai By A v ∈ I.Lf :=
  fun v hv => hAi _ (sub_one_Lf hBy _ (hA v hv))

theorem Tm_mL (m : ℕ) {Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hAi : ∀ v ∈ I.Lf, Ai *ᵥ v ∈ I.Lf) (hBy : ∀ v ∈ I.Lf, By *ᵥ v ∈ I.Lf) (hA : ∀ v ∈ I.Lf, A *ᵥ v ∈ I.Lf) :
    ∀ v ∈ mL I m, Tm Ai By A v ∈ mL I m := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Tm_smul]
    exact Submodule.subset_span ⟨_, Tm_Lf hAi hBy hA x hx, rfl⟩
  | zero =>
    have h0 : Tm Ai By A 0 = 0 := by simp [Tm]
    rw [h0]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [Tm_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have h1 : Tm Ai By A (a • x) = a • Tm Ai By A x := by
      rw [Subring.smul_def, Subring.smul_def, Tm_smul]
    rw [h1]
    exact Submodule.smul_mem _ a hx

end Grp

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem sig_eq : (starRingEnd X.B.I.E) = (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) := by
  first
  | rfl
  | exact RingHom.ext fun _ => rfl

theorem hA_e_f (a b : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.fR b)) = if a = b then 1 else 0 := by
  rw [hA_incl, sig_eq]
  have h := MassDataLevelSSteps.FrameW.hE_crdOf X (X.eX a) (X.fY b)
  change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
    (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.fY b))) = _
  rw [h, X.ef]
  split_ifs <;> simp

theorem hA_f_e (b a : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR b)) (incl X.B.I (X.eR a)) = if b = a then 1 else 0 := by
  rw [hA_incl, sig_eq]
  have h := MassDataLevelSSteps.FrameW.hE_crdOf X (X.fY b) (X.eX a)
  change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
    (crdOf X.B.I X.ιE X.bas (X.fY b)) (crdOf X.B.I X.ιE X.bas (X.eX a))) = _
  rw [h, ← LinearMap.isSymm_def.1 (VS D).herm (X.eX a) (X.fY b), X.ef]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

theorem key {c d : ℕ} (hfL : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR b) ∈ X.B.I.Lf)
    (hec : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g)
    {s : Set (Fin D.R.rS)} {w : VA X.B.I}
    (hw : w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s))
    (hdw : (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈ X.B.I.Lf) :
    ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈
      Submodule.span (IntAf X.B.I.F X.B.I.E) (X.e0 '' s) ⊔ mL X.B.I X.B.g := by
  classical
  obtain ⟨l, hls, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 hw
  have hsum : Finsupp.linearCombination (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (fun b => incl X.B.I (X.eR b)) l =
      ∑ b, l b • incl X.B.I (X.eR b) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; exact zero_smul _ _
  rw [hsum] at hdw ⊢
  have hcoef : ∀ b, ((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b ∈ IntAf X.B.I.F X.B.I.E := by
    intro b
    have h := hA_int X.B.I _ (hfL b) _ hdw
    rw [hA_nat_left, hA_smul_right, hA_sum_right] at h
    simp only [hA_smul_right, hA_f_e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true] at h
    convert h using 1
    push_cast; ring
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : l b = 0
  · rw [hb, zero_smul, smul_zero]; exact zero_mem _
  have hbs : b ∈ s := hls (Finsupp.mem_support_iff.2 hb)
  have heq : ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (l b • incl X.B.I (X.eR b)) =
      (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 b) -
      (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) •
        ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b))) := by
    rw [← smul_sub, ← smul_sub, sub_sub_cancel]
    simp only [smul_smul]
    congr 1; push_cast; ring
  rw [heq]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (sm X.B.I (hcoef b) (hec b)))
  exact sm X.B.I (hcoef b) (sm X.B.I (natCast_int X.B.I c) (Submodule.subset_span ⟨b, hbs, rfl⟩))

theorem mults (u : D.what₂.Word) : ∃ c : ℕ, Nat.Coprime c X.B.g ∧
    (∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g) ∧
    (∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g) ∧
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) ∈
      mL X.B.I X.B.g := by
  have h1 : ∀ a, ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 a - incl X.B.I (X.eR a)) ∈ mL X.B.I X.B.g :=
    fun a => (X.basisApprox a).1
  have h2 : ∀ a, ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 a - incl X.B.I (X.fR a)) ∈ mL X.B.I X.B.g :=
    fun a => (X.basisApprox a).2
  have h3 : ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) ∈
        mL X.B.I X.B.g := X.xu_z u
  choose ce hce1 hce2 using h1
  choose cf hcf1 hcf2 using h2
  obtain ⟨cz, hcz1, hcz2⟩ := h3
  have hP : ∀ b, ce b * cf b ∣ ∏ a, ce a * cf a := fun b =>
    Finset.dvd_prod_of_mem (fun a => ce a * cf a) (Finset.mem_univ b)
  have hcop : Nat.Coprime ((∏ a, ce a * cf a) * cz) X.B.g :=
    Nat.Coprime.mul_left (Nat.Coprime.prod_left fun a _ => Nat.Coprime.mul_left (hce1 a) (hcf1 a)) hcz1
  have hd1 : ∀ b, ce b ∣ (∏ a, ce a * cf a) * cz := fun b =>
    Dvd.dvd.mul_right ((Dvd.intro (cf b) rfl).trans (hP b)) cz
  have hd2 : ∀ b, cf b ∣ (∏ a, ce a * cf a) * cz := fun b =>
    Dvd.dvd.mul_right ((Dvd.intro_left (ce b) rfl).trans (hP b)) cz
  have hd3 : cz ∣ (∏ a, ce a * cf a) * cz := Dvd.intro_left _ rfl
  exact ⟨(∏ a, ce a * cf a) * cz, hcop, fun b => dvd_smul X.B.I (hd1 b) (hce2 b),
    fun b => dvd_smul X.B.I (hd2 b) (hcf2 b), dvd_smul X.B.I hd3 hcz2⟩

end MassDataMassesW.NLev
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MassUnfoldHolds
section
noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

namespace MassDataMassesW

theorem massUnfold_holds : MassUnfold := by
  intro D X u hT _hc _hK hKo hfin 𝓕 h𝓕
  haveI : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have hU : MeasurableSet ((KH X u : Subgroup ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
    (hKo.preimage continuous_subtype_val).measurableSet
  exact massUnfold_gen X.B.I.cm.sig X.B.I.J (frameOf X u) (isCMExt_of_cmData X.B.I.cm)
    (isHermND_of_setting X) (X.measW u) hT (KH X u) hU hfin 𝓕 h𝓕

end MassDataMassesW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StabFiniteOf
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

theorem stabFinite_of (hH : HinfCompact) (hK : KCompactOpen) : StabFinite := by
  intro D X u x
  obtain ⟨e, he⟩ := splitIso_holds X.B.I.cm.sig X.B.I.J
  have hcK := (hK X).1
  have hcI : IsCompact ((Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J))) := by
    haveI := hH X u
    exact isCompact_iff_compactSpace.2 this
  have homogComponent_comm_second_action : IsCompact ((fun k => (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * k *
      (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)⁻¹) '' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) :=
    hcK.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hcK3 : IsCompact (e ⁻¹' ((Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) ×ˢ
        ((fun k => (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * k *
          (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)⁻¹) '' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))))) :=
    e.toHomeomorph.isCompact_preimage.2 (hcI.prod homogComponent_comm_second_action)
  haveI hdisc : DiscreteTopology ↥(show Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) from
      HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := discHF_setting X
  have pullback_fin_relation : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G)
      [DiscreteTopology Γ] (K : Set G), IsCompact K → Finite ↥((Subtype.val : Γ → G) ⁻¹' K) := by
    intro G _ _ _ Γ _ K hK
    obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
    have h1U : (1 : G) ∈ U := by
      have h0 : (1 : Γ) ∈ (Subtype.val : Γ → G) ⁻¹' U := by rw [hUeq]; exact Set.mem_singleton 1
      exact h0
    have hc : Continuous (fun p : G × G => p.1⁻¹ * p.2) := continuous_fst.inv.mul continuous_snd
    have hpre : (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' U ∈ nhds ((1 : G), (1 : G)) := by
      apply hc.continuousAt.preimage_mem_nhds
      simpa using hU.mem_nhds h1U
    obtain ⟨V1, hV1, V2, hV2, hVV⟩ := mem_nhds_prod_iff.1 hpre
    have hV1m : (1 : G) ∈ interior (V1 ∩ V2) := mem_interior_iff_mem_nhds.2 (Filter.inter_mem hV1 hV2)
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun k : K => (fun y => (k : G)⁻¹ * y) ⁻¹' interior (V1 ∩ V2))
      (fun k => isOpen_interior.preimage (continuous_const.mul continuous_id)) (by
        intro y hy
        exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, by rw [Set.mem_preimage, inv_mul_cancel]; exact hV1m⟩)
    have hch : ∀ s : ↥((Subtype.val : Γ → G) ⁻¹' K), ∃ i : t,
        ((((i : K) : G))⁻¹ * ((s : Γ) : G)) ∈ interior (V1 ∩ V2) := by
      intro s
      obtain ⟨i, hi, hs⟩ := Set.mem_iUnion₂.1 (ht s.2)
      exact ⟨⟨i, hi⟩, hs⟩
    choose f hf using hch
    refine Finite.of_injective f (fun s1 s2 h => ?_)
    have a1 := hf s1
    have a2 := hf s2
    rw [h] at a1
    have hmem : ((((f s2 : K) : G))⁻¹ * ((s1 : Γ) : G), (((f s2 : K) : G))⁻¹ * ((s2 : Γ) : G)) ∈ V1 ×ˢ V2 :=
      ⟨(interior_subset a1).1, (interior_subset a2).2⟩
    have hU' : ((((f s2 : K) : G))⁻¹ * ((s1 : Γ) : G))⁻¹ * ((((f s2 : K) : G))⁻¹ * ((s2 : Γ) : G)) ∈ U :=
      hVV hmem
    rw [show ((((f s2 : K) : G))⁻¹ * ((s1 : Γ) : G))⁻¹ * ((((f s2 : K) : G))⁻¹ * ((s2 : Γ) : G)) =
      ((s1 : Γ) : G)⁻¹ * ((s2 : Γ) : G) by group] at hU'
    have e1 : ((s1 : Γ)⁻¹ * (s2 : Γ) : Γ) ∈ (Subtype.val : Γ → G) ⁻¹' U := hU'
    rw [hUeq, Set.mem_singleton_iff, inv_mul_eq_one] at e1
    exact Subtype.ext e1
  haveI := pullback_fin_relation _ (show Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) from
    HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) _ hcK3
  have hsurj : ∀ t : ↥(GamH X u ⊓ (KH X u).map (MulAut.conj x).toMonoidHom),
      ∃ γ : Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u),
        γ ∈ ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) ∧
          prjF X.B.I.cm.sig X.B.I.J (frameOf X u) γ = t := by
    intro t
    have ht : (t : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) ∈
        (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))).map
          (prjF X.B.I.cm.sig X.B.I.J (frameOf X u)) := by
      rw [prjF_map_ratOf]
      exact t.2.1
    obtain ⟨γ, hγ, hγt⟩ := Subgroup.mem_map.1 ht
    exact ⟨γ, hγ, hγt⟩
  choose γ hγ hγt using hsurj
  refine Finite.of_injective (fun t => (⟨⟨(γ t : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J),
    Subgroup.mem_comap.1 (hγ t)⟩, ?_⟩ : ((↑) ⁻¹' (e ⁻¹' ((Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) ×ˢ
        ((fun k => (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * k *
          (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)⁻¹) '' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))))) :
      Set ↥(show Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) from HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)))) ?_
  · simp only [Set.mem_preimage]
    rw [he]
    refine ⟨?_, ?_⟩
    · exact haMap_stabT X.B.I.cm.sig X.B.I.J (fstA X.B.I.F) (tupH (frameOf X u)) (γ t) (γ t).2
    · show (splitA X.B.I.cm.sig X.B.I.J (γ t : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).2 ∈
        (_ : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))
      rw [← prjF_val, hγt t]
      obtain ⟨k, hk, hkt⟩ := Subgroup.mem_map.1 t.2.2
      rw [← hkt]
      refine ⟨(k : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J), Subgroup.mem_subgroupOf.1 hk, ?_⟩
      simp [MulAut.conj_apply]
  · intro t1 t2 h
    have h1 : (γ t1 : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) = γ t2 := by
      have h0 := congrArg (fun z => z.1.1) h
      simpa using h0
    have h2 : γ t1 = γ t2 := Subtype.ext h1
    apply Subtype.ext
    rw [← hγt t1, ← hγt t2, h2]

end MassDataMassesW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.TensLiftSelf
section
noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def pv (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → Af F ⊗[F] E) : Fin n → Fv F v ⊗[F] E :=
  fun i => tensMap (E := E) (evalV F v) (x i)

def latHat (Λ : Set (Fin n → E)) : Set (Fin n → Af F ⊗[F] E) :=
  {x | ∀ v, pv v x ∈ latLoc (E := E) v Λ}

theorem pv_mulVec (v : HeightOneSpectrum (𝓞 F)) (m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))
    (x : Fin n → Af F ⊗[F] E) :
    pv v (m *ᵥ x) = (m.map (tensMap (E := E) (evalV F v))) *ᵥ pv v x := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [pv, Matrix.mulVec, dotProduct, map_sum]

open Classical in
theorem singleV_smul (v : HeightOneSpectrum (𝓞 F)) (c : F) (y : Fv F v) :
    singleV F v (c • y) = c • singleV F v y := by
  apply RestrictedProduct.ext
  intro j
  show (singleV F v (c • y)) j = evalV F j (c • singleV F v y)
  rw [map_smul]
  show _ = c • (singleV F v y) j
  by_cases h : j = v
  · subst h
    rw [PI.VolStabSW.VolAAW.singleV_self, PI.VolStabSW.VolAAW.singleV_self]
  · rw [PI.VolStabSW.VolAAW.singleV_ne _ _ h, PI.VolStabSW.VolAAW.singleV_ne _ _ h, smul_zero]

def sV (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] Af F where
  toFun := singleV F v
  map_add' := PI.VolStabSW.SdUniqW.singleV_add v
  map_smul' := singleV_smul v

def liftV (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E) : Fin n → Af F ⊗[F] E :=
  fun i => LinearMap.rTensor E (sV v) (y i)

theorem tens_lift_self (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    tensMap (E := E) (evalV F v) (LinearMap.rTensor E (sV v) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [LinearMap.rTensor_tmul]
    show (evalV F v (singleV F v a)) ⊗ₜ[F] e = a ⊗ₜ e
    show (singleV F v a v) ⊗ₜ[F] e = a ⊗ₜ e
    rw [PI.VolStabSW.VolAAW.singleV_self]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem tens_lift_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (z : Fv F v ⊗[F] E) :
    tensMap (E := E) (evalV F w) (LinearMap.rTensor E (sV v) z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [LinearMap.rTensor_tmul]
    show (evalV F w (singleV F v a)) ⊗ₜ[F] e = 0
    show (singleV F v a w) ⊗ₜ[F] e = 0
    rw [PI.VolStabSW.VolAAW.singleV_ne _ _ h, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem pv_liftV_self (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E) : pv v (liftV v y) = y := by
  funext i
  exact tens_lift_self v (y i)

theorem pv_liftV_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fin n → Fv F v ⊗[F] E) :
    pv w (liftV v y) = 0 := by
  funext i
  exact tens_lift_ne h (y i)

theorem liftV_mem (Λ : Set (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v Λ) : liftV v y ∈ latHat (F := F) Λ := by
  intro w
  by_cases h : w = v
  · subst h
    rw [pv_liftV_self]
    exact hy
  · rw [pv_liftV_ne h]
    exact zero_mem _

theorem loc_of_matStab (Λ : Set (Fin n → E)) {m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)}
    (hm : m ∈ matStab (latHat (F := F) Λ)) (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v Λ) : (m.map (tensMap (E := E) (evalV F v))) *ᵥ y ∈ latLoc (E := E) v Λ := by
  have h := hm _ (liftV_mem Λ v hy) v
  rwa [pv_mulVec, pv_liftV_self] at h

end Lift

end MassDataMassesW.KCptW
end
end

