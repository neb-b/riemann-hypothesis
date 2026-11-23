module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.CxPassMet
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.ExistsSumOfMemISup
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

section Spec

variable {K : Type} [Field K]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type} [Fintype ι]

theorem exists_sum_of_mem_iSup {R M : Type} [Ring R] [AddCommGroup M] [Module R M] {ι : Type} [Fintype ι]
    (Q : ι → Submodule R M) {y : M} (hy : y ∈ ⨆ p, Q p) : ∃ ys : ι → M, (∀ p, ys p ∈ Q p) ∧ ∑ p, ys p = y := by
  classical
  refine Submodule.iSup_induction Q (motive := fun y => ∃ ys : ι → M, (∀ p, ys p ∈ Q p) ∧ ∑ p, ys p = y) hy ?_ ?_ ?_
  · intro i x hx
    refine ⟨Pi.single i x, fun p => ?_, ?_⟩
    · by_cases h : p = i
      · subst h; simpa using hx
      · simp [h]
    · simp [Finset.sum_pi_single']
  · exact ⟨0, fun _ => zero_mem _, by simp⟩
  · rintro x y ⟨xs, hxs, rfl⟩ ⟨ys, hys, rfl⟩
    exact ⟨xs + ys, fun p => add_mem (hxs p) (hys p), by simp [Finset.sum_add_distrib]⟩

def specOp (U : ι → Submodule ℂ E) (a : ι → ℂ) : Module.End ℂ E :=
  ∑ p, a p • ((U p).starProjection : E →L[ℂ] E).toLinearMap

theorem specOp_apply (U : ι → Submodule ℂ E) (a : ι → ℂ) (x : E) :
    specOp U a x = ∑ p, a p • (U p).starProjection x := by
  simp [specOp, LinearMap.sum_apply]

theorem proj_mem (U : ι → Submodule ℂ E) (p : ι) (x : E) : (U p).starProjection x ∈ U p := by
  exact Submodule.starProjection_apply_mem (U p) x

variable (U : ι → Submodule ℂ E) (hU : ∀ p q, p ≠ q → ∀ x ∈ U p, ∀ y ∈ U q, ⟪x, y⟫_ℂ = 0)
include hU

theorem proj_of_mem [DecidableEq ι] {p q : ι} {x : E} (hx : x ∈ U q) :
    (U p).starProjection x = if p = q then x else 0 := by
  split_ifs with h
  · subst h
    exact Submodule.starProjection_eq_self_iff.2 hx
  · have ho : x ∈ (U p)ᗮ := (Submodule.mem_orthogonal _ _).2 fun u hu => hU p q h u hu x hx
    have h1 := Submodule.starProjection_eq_self_iff.2 ho
    rw [Submodule.starProjection_orthogonal_val] at h1
    exact sub_eq_self.1 h1

theorem specOp_of_mem {a : ι → ℂ} {q : ι} {x : E} (hx : x ∈ U q) : specOp U a x = a q • x := by
  classical
  rw [specOp_apply]
  simp only [proj_of_mem U hU hx, smul_ite, smul_zero]
  simp

theorem proj_specOp (a : ι → ℂ) (q : ι) (x : E) :
    (U q).starProjection (specOp U a x) = a q • (U q).starProjection x := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [specOp_apply, map_sum, Finset.sum_eq_single q]
  · rw [map_smul, Submodule.starProjection_eq_self_iff.2 (proj_mem U q x)]
  · intro p _ hp
    rw [map_smul, proj_of_mem U hU (proj_mem U p x), if_neg (Ne.symm hp), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ q) h

theorem sum_proj {x : E} (hx : x ∈ ⨆ p, U p) : ∑ p, (U p).starProjection x = x := by
  classical
  refine Submodule.iSup_induction U (motive := fun x => ∑ p, (U p).starProjection x = x) hx ?_ ?_ ?_
  · intro q x hx
    simp only [proj_of_mem U hU hx]
    simp
  · simp
  · intro x y hx hy
    simp only [map_add (f := _), Finset.sum_add_distrib, hx, hy]


omit hU in
theorem specOp_mem (a : ι → ℂ) (W : Submodule ℂ E) (hUW : ∀ p, U p ≤ W) (x : E) : specOp U a x ∈ W := by
  rw [specOp_apply]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hUW p (proj_mem U p x))

end Spec

section SpecW

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type} [Fintype ι]

theorem spec_eig (σ : K →+* ℂ) {H : Type} (P : ι → Submodule ℂ E) (W : Submodule ℂ E) (e : ι → H → K)
    (he : Function.Injective e) (hO : ∀ p q, p ≠ q → ∀ x ∈ P p ⊓ W, ∀ y ∈ P q ⊓ W, ⟪x, y⟫_ℂ = 0)
    (hS : (⨆ p, P p ⊓ W) = W) (c : ι) :
    P c ⊓ W = (⨅ T, LinearMap.ker (specOp (fun p => P p ⊓ W) (fun p => σ (e p T)) - σ (e c T) • LinearMap.id)) ⊓ W := by
  apply le_antisymm
  · intro x hx
    refine ⟨(Submodule.mem_iInf _).2 fun T => ?_, hx.2⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, specOp_of_mem (fun p => P p ⊓ W) hO hx]
    simp
  · rintro x ⟨hx, hW⟩
    have hT : ∀ T, specOp (fun p => P p ⊓ W) (fun p => σ (e p T)) x = σ (e c T) • x := fun T => by
      have h := (Submodule.mem_iInf _).1 hx T
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
      simpa using h
    have h0 : ∀ q, q ≠ c → (P q ⊓ W).starProjection x = 0 := by
      intro q hq
      obtain ⟨T, hTq⟩ : ∃ T, e q T ≠ e c T := by
        by_contra h
        push Not at h
        exact hq (he (funext h))
      have h1 := proj_specOp (fun p => P p ⊓ W) hO (fun p => σ (e p T)) q x
      rw [hT T, map_smul] at h1
      have h2 : (σ (e q T) - σ (e c T)) • (P q ⊓ W).starProjection x = 0 := by
        rw [sub_smul, ← h1, sub_self]
      rcases smul_eq_zero.1 h2 with h3 | h3
      · exact absurd (σ.injective (sub_eq_zero.1 h3)) hTq
      · exact h3
    have hx' : x ∈ ⨆ p, P p ⊓ W := by rw [hS]; exact hW
    have hsum := sum_proj (fun p => P p ⊓ W) hO hx'
    rw [Finset.sum_eq_single c (fun q _ hq => h0 q hq) (fun h => absurd (Finset.mem_univ c) h)] at hsum
    rw [← hsum]
    exact proj_mem (fun p => P p ⊓ W) c x

theorem spec_rat (σ : K →+* ℂ) {D : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f) (P : ι → Submodule ℂ E)
    (a : ι → K) (hO : ∀ p q, p ≠ q → ∀ x ∈ P p ⊓ LinearMap.range f, ∀ y ∈ P q ⊓ LinearMap.range f, ⟪x, y⟫_ℂ = 0)
    (hK : ∀ y : Fin D → K, y ∈ ⨆ p, (P p).comap (f.comp (cptL σ D))) :
    IsRat σ (relMat f (specOp (fun p => P p ⊓ LinearMap.range f) (fun p => σ (a p)) ∘ₗ f)) := by
  classical
  intro i k
  obtain ⟨ys, hys, hsum⟩ := exists_sum_of_mem_iSup _ (hK (Pi.single k 1))
  have hmem : ∀ p, f (cpt σ (ys p)) ∈ P p ⊓ LinearMap.range f := fun p => ⟨hys p, ⟨_, rfl⟩⟩
  have hcs : ∀ z : ι → Fin D → K, cpt σ (∑ p, z p) = ∑ p, cpt σ (z p) := fun z => by
    funext l
    simp [cpt, Finset.sum_apply]
  have hk : (Pi.single k 1 : Fin D → ℂ) = cpt σ (∑ p, ys p) := by
    rw [hsum]
    funext l
    by_cases h : l = k
    · subst h; simp [cpt]
    · simp [cpt, h]
  have key : (specOp (fun p => P p ⊓ LinearMap.range f) (fun p => σ (a p)) ∘ₗ f) (Pi.single k 1) =
      f (cpt σ (∑ p, a p • ys p)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.comp_apply, hk, hcs, map_sum, map_sum, hcs, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [specOp_of_mem (fun p => P p ⊓ LinearMap.range f) hO (hmem p), cpt_smul, map_smul]
  refine ⟨(∑ p, a p • ys p) i, ?_⟩
  simp only [relMat, Matrix.of_apply]
  rw [key, hf (solve_spec f (⟨_, rfl⟩ : f (cpt σ (∑ p, a p • ys p)) ∈ LinearMap.range f))]
  rfl

end SpecW

section Structs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} {X : CxData A} {fc : DefSub A → DefFace Bs} {cr : Crd A fc} {b : Bool}

theorem rowsK (hW : (lv (fc X.zs) b).WF) (h3 : X.H3 cr b) (y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    y ∈ ⨆ p, X.Ep cr b p := by
  have hle : (⨆ p, (lv (fc X.zs) b).Qp Bs.μ0 p) ≤ ⨆ p, X.Ep cr b p :=
    iSup_mono fun p x hx => (X.mem_Ep cr b p x).2 ((h3 p x).1 hx)
  exact hle (hW.Qp_top ▸ Submodule.mem_top)

theorem liftsK (ht : (lv (fc X.zs) b).Types) (hk : X.KForm b) (he : X.EWnorm b) (hn : 0 < X.nP b) (h5 : X.H5 cr b)
    (hr : X.RATth cr b) (h3W : X.H3W cr b) (j : Bs.J) (y : Fin (X.dW b j) → K) : y ∈ ⨆ p, X.WpK b j p := by
  obtain ⟨x, rfl⟩ := (X.liftMat_bij cr b hk he hn h5 hr j Bs.μ0).2 y
  have hx : x ∈ ⨆ p, (lv (fc X.zs) b).Zp j Bs.μ0 p := by
    rw [ht j]
    exact Submodule.mem_top
  have hle : (⨆ p, (lv (fc X.zs) b).Zp j Bs.μ0 p).map (X.liftMat cr b j Bs.μ0).mulVecLin ≤ ⨆ p, X.WpK b j p := by
    rw [Submodule.map_iSup]
    exact iSup_mono fun p => Submodule.map_le_iff_le_comap.2 fun z hz => by
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, X.mem_WpK b j p, X.key_lift cr b h5 hr j Bs.μ0 z]
      exact (h3W j p z).1 hz
  exact hle (Submodule.mem_map_of_mem hx)

theorem heckeRows_spec (h2 : X.H2 cr b) (hE : X.PartsE b) (hQ : ∀ y, y ∈ ⨆ p, X.Ep cr b p) (cf : ConvFace Bs) :
    Nonempty (X.HeckeRowsC cr b cf) := by
  have hO' : ∀ p q, p ≠ q → ∀ x ∈ X.EEp p ⊓ LinearMap.range (X.iC cr b Bs.μ0),
      ∀ y ∈ X.EEp q ⊓ LinearMap.range (X.iC cr b Bs.μ0), ⟪x, y⟫_ℂ = 0 := by
    rw [h2.2.2]
    exact hE.1
  refine ⟨{ hC := fun T => specOp (fun p => X.EEp p ⊓ X.EEl b) (fun p => Bs.v0.embedding (cf.ev p T)),
            maps := fun T e _ => specOp_mem _ _ _ (fun _ => inf_le_right) e,
            rat := fun T => ?_,
            eig := fun c => spec_eig Bs.v0.embedding X.EEp (X.EEl b) cf.ev cf.ev_inj hE.1 hE.2 c }⟩
  have h := spec_rat Bs.v0.embedding (X.iC cr b Bs.μ0) h2.1 X.EEp (fun p => cf.ev p T) hO' hQ
  rw [h2.2.2] at h
  exact h

theorem heckeW_spec (hk : X.KForm b) (he : X.EWnorm b) (hn : 0 < X.nP b) (hP : X.PartsW b)
    (hK : ∀ j y, y ∈ ⨆ p, X.WpK b j p) (cf : ConvFace Bs) : Nonempty (X.HeckeWC b cf) :=
  ⟨{ hC := fun j T => specOp (fun p => X.Wp j p ⊓ LinearMap.range (X.w0C b j)) (fun p => Bs.v0.embedding (cf.ev p T)),
     maps := fun _ _ _ => specOp_mem _ _ _ (fun _ => inf_le_right) _,
     rat := fun j T => spec_rat Bs.v0.embedding (X.w0C b j) (X.principal_form_injective b hk he hn j) (X.Wp j) (fun p => cf.ev p T)
       (hP j).1 (hK j),
     eig := fun j c => spec_eig Bs.v0.embedding (X.Wp j) (LinearMap.range (X.w0C b j)) cf.ev cf.ev_inj (hP j).1 (hP j).2 c }⟩

end CxData

end Structs

section Fields3

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {X : CxData A3.fam3.amb3} {s : ℕ}
  {C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
  {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)}

theorem heckeRB_of (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (cf : ConvFace A3.fam3.base3) :
    Nonempty (X.HeckeRowsC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false cf) :=
  CxData.heckeRows_spec (hR.what₂ false).1 (hR.partsE false)
    (CxData.rowsK (hR.rowHyp false).wf (hR.rowHyp false).h3) cf

theorem heckeRC_of (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (cf : ConvFace A3.fam3.base3) :
    Nonempty (X.HeckeRowsC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true cf) :=
  CxData.heckeRows_spec (hR.what₂ true).1 (hR.partsE true)
    (CxData.rowsK (hR.rowHyp true).wf (hR.rowHyp true).h3) cf

theorem heckeWB_of (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (cf : ConvFace A3.fam3.base3) :
    Nonempty (X.HeckeWC false cf) :=
  CxData.heckeW_spec hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.partsW
    (CxData.liftsK hR.types0 hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.lifts0.1 hR.ratTh hR.liftHyp0.h3W) cf

end Fields3

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.MajorantAtBaseEqInnerOfPackage
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

section Part3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty : Type}

theorem mem_part3_iff (B : BlockDat K G Pl0) (D : InertDat3 B I0 Ty) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)
    (p : Typ3 K Pl0 I0 Ty) (y : Fin (B.dZ ℓ Z) → K) : y ∈ D.part3 ℓ Z p ↔ B.toF ℓ Z y ∈ D.inertTypeEigenspaceSum p := by
  rw [InertDat3.inert_part_eq_comap]; rfl

end Part3

open Formalism.IndefR.CxPass.In

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

theorem side_lv (b : Bool) :
    lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b = I.A3.side3 (I.lvP b) (I.lvψ b) I.X.zs := by
  cases b <;> rfl

theorem pFrames : I.PFrames := by
  intro s h v
  have hW := I.A3.side_well_formed h.ok ⊥ 1 I.X.zs h.stable h.inBlock h.sep
  have hu : IsUnit (frameOf ((prin I.X).gramE I.cg false)).det :=
    gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)
  exact (rowXE_spec (Df := I.A3.side3 ⊥ 1 I.X.zs) hW _ hu I.X.κ h.h4pos.1 (fun j p v => I.X.lam j I.A3.fam3.base3.μ0 p v)
    (fun j p v => h.h4pos.2.1 j _ p v)).1 v

variable {I} in
theorem Z_stable_g {s : ℕ} (h : I.Hyp s) (g : G) :
    I.X.zs.Z I.A.fam.μ0 ≤ (I.X.zs.Z I.A.fam.μ0).comap ((I.A.fam.R I.A.fam.μ0).r g) := fun _ hz =>
  h.stable.1 I.A.fam.μ0 (Sum.inr g) (Submodule.mem_map_of_mem hz)

variable {I} in
theorem toF_rho (hρ : I.PRho) {s : ℕ} (h : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) (I.ρf g *ᵥ x) =
      (I.A.fam.R I.A.fam.μ0).r g ((I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) x) := by
  obtain ⟨y, hty⟩ := exists_toF_act (I.A.fam.R I.A.fam.μ0) h.ok.ok2.conj (h.ok.ok2.what₂ _) I.A.fam.X h.ok.ok2.irr
    (I.X.zs.Z I.A.fam.μ0) (fun g => Z_stable_g h g) g x
  have key : I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.ρf g *ᵥ x)) = I.iCg (cpt I.A3.fam3.base3.v0.embedding y) := by
    rw [(hρ s h).2.2 g x]
    have e1 : I.iCg (cpt I.A3.fam3.base3.v0.embedding x) =
        I.X.Θ I.A.fam.μ0 (I.X.jR I.A.fam.μ0 ((I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) x)) :=
      iC_cpt I.X I.cg false I.A.fam.μ0 x
    have e2 : I.iCg (cpt I.A3.fam3.base3.v0.embedding y) =
        I.X.Θ I.A.fam.μ0 (I.X.jR I.A.fam.μ0 ((I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) y)) :=
      iC_cpt I.X I.cg false I.A.fam.μ0 y
    rw [e1, e2]
    erw [hty]
    exact (h.gequiv I.A.fam.μ0 g _).symm
  have hxy := cpt_injective _ (h.h2g.1 key)
  exact (congrArg (fun z => (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) z) hxy).trans hty

variable {I} in
theorem wf_lv {s : ℕ} (h : I.Hyp s) (b : Bool) : (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).WF := by
  rw [side_lv]; exact I.A3.side_well_formed h.ok _ _ _ h.stable h.inBlock h.sep

variable {I} in
theorem wf_g {s : ℕ} (h : I.Hyp s) : (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).WF :=
  I.A3.side_well_formed h.ok ⊥ 1 _ h.stable h.inBlock h.sep


variable {I} in
theorem opAll_comm {s : ℕ} (h : I.Hyp s) (g : G) (k : (I.A3.rowI I.A.fam.μ0).OpIx) :
    Commute ((I.A3.rowI I.A.fam.μ0).opAll k) ((I.A.fam.R I.A.fam.μ0).r g) := by
  rcases k with i | k
  · exact (h.ok.ok2.what₂ _).opG i g
  · exact (h.ok.what₂ _).opG k g

variable {I} in
theorem Jm_parts (hJt : I.PJt) {s : ℕ} (h : I.Hyp s) (b : Bool) (p : I.A3.fam3.base3.Ix)
    (x : Fin ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ I.A3.fam3.base3.μ0) → K)
    (hx : x ∈ (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).Qp I.A3.fam3.base3.μ0 p) :
    I.Jm b *ᵥ x ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Qp I.A3.fam3.base3.μ0 p := by
  cases b
  · refine (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 (I.Jm false *ᵥ x)).2 ?_
    have e : (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) (I.Jm false *ᵥ x) =
        (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl I.P0 I.ψ0) (I.X.zs.Z I.A.fam.μ0) x := (hJt s h false I.A.fam.μ0).2.1 x
    rw [e]
    exact (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl I.P0 I.ψ0) (I.X.zs.Z I.A.fam.μ0) p.1 x).1 hx
  · refine (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 (I.Jm true *ᵥ x)).2 ?_
    have e : (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) (I.Jm true *ᵥ x) =
        (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl I.P1 I.ψ1) (I.X.zs.Z I.A.fam.μ0) x := (hJt s h true I.A.fam.μ0).2.1 x
    rw [e]
    exact (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl I.P1 I.ψ1) (I.X.zs.Z I.A.fam.μ0) p.1 x).1 hx

variable {I} in
theorem quot_lv (hT : TransferS (K := K) (G := G) (Pl0 := Pl0)) (hJt : I.PJt) {s : ℕ} (h : I.Hyp s) (b : Bool)
    (v : InfinitePlace K)
    (x y : Fin ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ I.A3.fam3.base3.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).XQ I.A3.fam3.base3.μ0) v x y =
      (((Nat.card (I.lvP b) : ℝ)⁻¹ : ℝ) : ℂ) *
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).XQ I.A3.fam3.base3.μ0) v
          (I.Jm b *ᵥ x) (I.Jm b *ᵥ y) := by
  cases b
  · exact hT (I.A.fam.R I.A.fam.μ0) h.ok.ok2.conj (h.ok.ok2.what₂ _) I.A.fam.X h.ok.ok2.irr I.P0 I.ψ0 (I.X.zs.Z I.A.fam.μ0)
      (fun g => Z_stable_g h g) (I.Jm false) (hJt s h false I.A.fam.μ0).2.1 v x y
  · exact hT (I.A.fam.R I.A.fam.μ0) h.ok.ok2.conj (h.ok.ok2.what₂ _) I.A.fam.X h.ok.ok2.irr I.P1 I.ψ1 (I.X.zs.Z I.A.fam.μ0)
      (fun g => Z_stable_g h g) (I.Jm true) (hJt s h true I.A.fam.μ0).2.1 v x y

variable {I} in
theorem majorant_at_base_eq_inner {s : ℕ} (h : I.Hyp s) (x y : Fin I.Sg.D → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE I.A3.fam3.base3.v0 x y =
      ⟪I.iCg (cpt I.A3.fam3.base3.v0.embedding x), I.iCg (cpt I.A3.fam3.base3.v0.embedding y)⟫_ℂ := by
  have e := majorant_at_base_eq_scaled_inner (prin I.X) I.cg false (wf_g h) h.h2g.1 (show (0 : ℝ) < 1 by norm_num) h.h4pos.1
    (fun j p v => h.h4pos.2.1 j _ p v) x y
  have e1 : (prin I.X).nP false = 1 := rfl
  rw [e1, inv_one, Complex.ofReal_one, one_mul] at e
  exact e

variable {I} in
theorem majorant_at_base_eq_inner_of_package {s : ℕ} (h : I.Hyp s) (b : Bool) (x y : Fin (I.Sb b).D → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (I.Sb b).D)) (I.Sb b).XE I.A3.fam3.base3.v0 x y =
      (((I.X.nP b)⁻¹ : ℝ) : ℂ) *
        ⟪I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x),
          I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y)⟫_ℂ :=
  majorant_at_base_eq_scaled_inner I.X I.cr b (wf_lv h b) (h.h2 b).1 (h.h4pos.2.2 b) h.h4pos.1 (fun j p v => h.h4pos.2.1 j _ p v) x y

variable {I} in
theorem nP_eq_card_lvP {s : ℕ} (h : I.Hyp s) (b : Bool) : I.X.nP b = (Nat.card (I.lvP b) : ℝ) := by
  cases b
  · exact h.np0
  · exact h.np1

theorem pMet_core (hT : TransferS (K := K) (G := G) (Pl0 := Pl0)) (hsc : ∀ {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (c : ℝ), 0 < c → ∀ (v : InfinitePlace K) (x y : Fin n → K),
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (Formalism.BranchingDeterminantCap.scaleFrame c X) v x y =
        (((c ^ 2)⁻¹ : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y)
    (hJt : I.PJt) (hJ : I.PJ) : I.PMet := by
  intro s h b v x y
  have hcard : (0 : ℝ) < (Nat.card (I.lvP b) : ℝ) := by exact_mod_cast Nat.card_pos
  rw [hsc _ _ (Real.sqrt_pos.2 hcard), Real.sq_sqrt hcard.le]
  by_cases hv : v = I.A3.fam3.base3.v0
  · subst hv
    rw [majorant_at_base_eq_inner_of_package h b, majorant_at_base_eq_inner h, nP_eq_card_lvP h b]
    congr 1
    exact (congrArg₂ (fun a c => ⟪a, c⟫_ℂ) ((hJ s h b).1 x) ((hJ s h b).1 y)).symm
  · exact rowXE_map (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b)
      (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false) (wf_lv h b) (wf_g h) _
      (gramE_unit' I.X I.cr b (h.h2 b).1 (h.h4pos.2.2 b)) _
      (gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)) I.X.κ h.h4pos.1
      (fun j p v => I.X.lam j I.A3.fam3.base3.μ0 p v) (fun j p v => h.h4pos.2.1 j _ p v) (I.Jm b)
      (fun p x hx => Jm_parts hJt h b p x hx) _ v hv (quot_lv hT hJt h b v) x y

variable {I} in
theorem rho_parts (hρ : I.PRho) {s : ℕ} (h : I.Hyp s) (g : G) (p : I.A3.fam3.base3.Ix)
    (x : Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ I.A3.fam3.base3.μ0) → K)
    (hx : x ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Qp I.A3.fam3.base3.μ0 p) :
    I.ρf g *ᵥ x ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Qp I.A3.fam3.base3.μ0 p := by
  have hx' := (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 x).1 hx
  refine (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 (I.ρf g *ᵥ x)).2 ?_
  rw [toF_rho hρ h g x]
  exact Formalism.L2.Col.eigSum_le_comap (fun k => opAll_comm h g k) _ hx'

theorem pUni_core (hI : InvS (K := K) (G := G) (Pl0 := Pl0)) (hρ : I.PRho) : I.PUni := by
  intro s h v g x y
  by_cases hv : v = I.A3.fam3.base3.v0
  · subst hv
    rw [majorant_at_base_eq_inner h, majorant_at_base_eq_inner h]
    exact (congrArg₂ (fun a c => ⟪a, c⟫_ℂ) ((hρ s h).2.2 g x) ((hρ s h).2.2 g y)).trans (h.gunit g _ _)
  · have e := rowXE_map (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false)
      (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false) (wf_g h) (wf_g h) _
      (gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)) _
      (gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)) I.X.κ h.h4pos.1
      (fun j p v => I.X.lam j I.A3.fam3.base3.μ0 p v) (fun j p v => h.h4pos.2.1 j _ p v) (I.ρf g)
      (fun p x hx => rho_parts hρ h g p x hx) 1 v hv
      (fun x y => by
        rw [one_mul]
        exact (hI (I.A.fam.R I.A.fam.μ0) h.ok.ok2.conj (h.ok.ok2.what₂ _) I.A.fam.X h.ok.ok2.irr (I.X.zs.Z I.A.fam.μ0)
          (fun g => Z_stable_g h g) g (I.ρf g) (toF_rho hρ h g) v x y).symm) x y
    rw [one_mul] at e
    exact e.symm

theorem pMet_of (hJt : I.PJt) (hJ : I.PJ) : I.PMet :=
  I.pMet_core transferS_holds (fun X c hc v x y => BlockMetrics.majAt_scaleFrame X c hc v x y) hJt hJ

theorem pUni_of (_hJt : I.PJt) (hρ : I.PRho) : I.PUni :=
  I.pUni_core invS_holds hρ

end In3

end Formalism.IndefR.CxPass
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsBaseLevel
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {X : CxData A3.fam3.amb3} {s : ℕ}
  {C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
  {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)}

def indefiniteDataAtBaseLevel (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    IndefRows (lv (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) false) :=
  X.rowsOfR (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false (hR.rowHyp false) hR.liftHyp0 (hR.pos false) hR.proviso0
    hR.types0 hR.h0
    (CxData.cutDims X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false (hR.wf false) hR.h4pos hR.kForm hR.ewNorm hR.types0
      (hR.what₂ false).1 (hR.ratMu false) (hR.rowHyp false).h3 hR.lifts0.1 hR.ratTh hR.liftHyp0.h3W (hR.partsE false)
      hR.partsW hR.dimParts)

theorem subspaces_stable_in_block (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) : X.zs.Stable ∧ X.zs.InBlock :=
  ⟨hR.stable, hR.inBlock⟩

end Formalism.IndefR.Cx
end
end

