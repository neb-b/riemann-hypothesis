module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdND
section
noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem stepD (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0)
    (Λ Λ₃ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (hSD : SD S Λ) (hΛ₃fg : Λ₃.FG)
    (hfull₃ : ∀ u : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ Λ₃) (hSD₃ : SD S Λ₃)
    (hM : ∀ x ∈ orth S X, x ∈ Λ₃ ↔ x ∈ Λ) (htr : ∃ c : E, IsIntegral ℤ c ∧ c + star c = 1) :
    ∃ n : S.V ≃ₗ[E] S.V, (∀ a b, S.hT (n a) (n b) = S.hT a b) ∧ (∀ x ∈ orth S X, n x = x) ∧
      (n : S.V → S.V) '' Λ₃ = Λ := by
  classical
  obtain ⟨c, hcI, hc⟩ := htr
  have hXo := X_le_orth S X hXiso

  have hsurj : ∀ x ∈ Λ₃, ∃ y ∈ Λ, y - x ∈ X := fun x hx => by
    obtain ⟨w, hw, hxw⟩ := dual_sum S Λ hΛ hSD (orth S X) x
      (fun m hmΛ hmU => sd_int hSD₃ hx ((hM m hmU).2 hmΛ))
    refine ⟨w, hw, ?_⟩
    have : x - w ∈ X := mem_of_orth_orth S X fun u hu => by
      rw [hsw S u (x - w), orth_X S hxw hu, star_zero]
    have h2 := X.neg_mem this
    rwa [neg_sub] at h2
  obtain ⟨δ, hδX, hδ0, hδΛ⟩ := glift S Λ₃ Λ hΛ₃fg X (orth S X) (fun x hx hxo => (hM x hxo).1 hx) hsurj
  obtain ⟨B₀, hB₀⟩ := ext_top S (W := S.V) Λ₃ hfull₃ δ
  have hscale : ∀ v : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ ∃ hm : ((d : E) • v) ∈ Λ₃, (d : E) • B₀ v = δ ⟨_, hm⟩ := fun v => by
    obtain ⟨d, hd, hdv⟩ := hfull₃ v
    rw [oSmul] at hdv
    exact ⟨d, hd, hdv, by rw [← map_smul, hB₀ _ hdv]⟩
  have hB₀X : ∀ v, B₀ v ∈ X := fun v => by
    obtain ⟨d, hd, hm, he⟩ := hscale v
    have h1 : (d : E) • B₀ v ∈ X := by rw [he]; exact hδX _
    have h2 := X.smul_mem ((d : E)⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ (coe_ne_zero hd), one_smul] at h2
  have hB₀o : ∀ u ∈ orth S X, B₀ u = 0 := fun u hu => by
    obtain ⟨d, hd, hm, he⟩ := hscale u
    rw [hδ0 _ ((orth S X).smul_mem _ hu)] at he
    exact (smul_eq_zero.1 he).resolve_left (coe_ne_zero hd)

  let b := S.frame
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis S.hT S.nondeg b
  let σL : Fin S.rank → S.V →ₗ[E] E := fun k => S.hT (B₀ (b k)) + S.hT (b k) ∘ₗ B₀
  let B₁ : S.V →ₗ[E] S.V := ∑ k, ((-c) • σL k).smulRight (bs k)
  have hB₁app : ∀ v, B₁ v = ∑ k, (-c * (S.hT (B₀ (b k)) v + S.hT (b k) (B₀ v))) • bs k := fun v => by
    show (∑ k, ((-c) • σL k).smulRight (bs k)) v = _
    rw [LinearMap.sum_apply]
    rfl
  have hB₁ : ∀ v v', S.hT (B₁ v) v' = -(star c) * (S.hT (B₀ v) v' + S.hT v (B₀ v')) := fun v v' => by
    have key : S.hT (B₁ v) = -(star c) • (S.hT (B₀ v) + S.hT v ∘ₗ B₀) := by
      apply b.ext
      intro k'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hB₁app, map_sum, LinearMap.sum_apply]
      simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul,
        LinearMap.add_apply, LinearMap.comp_apply]
      rw [Finset.sum_eq_single k']
      · rw [hsw S (b k') (bs k'), hbs k' k', if_pos rfl, star_one, mul_one, star_mul, star_neg, star_add,
          ← hsw S (B₀ (b k')) v, ← hsw S (b k') (B₀ v)]
        ring
      · intro k _ hk
        rw [hsw S (b k') (bs k), hbs k' k, if_neg (Ne.symm hk), star_zero, mul_zero]
      · simp
    rw [key]
    rfl
  let B : S.V →ₗ[E] S.V := B₀ + B₁
  have hBapp : ∀ v, B v = B₀ v + B₁ v := fun v => rfl
  have hB₁X : ∀ v, B₁ v ∈ X := fun v => mem_of_orth_orth S X fun u hu => by
    rw [hB₁, hB₀o u hu, map_zero, orth_X S hu (hB₀X v)]
    ring
  have hB₁o : ∀ u ∈ orth S X, B₁ u = 0 := fun u hu => S.nondeg.1 _ fun v' => by
    rw [hB₁, hB₀o u hu, map_zero, LinearMap.zero_apply, orth_X' S hu (hB₀X v')]
    ring
  have hBX : ∀ v, B v ∈ X := fun v => by rw [hBapp]; exact X.add_mem (hB₀X v) (hB₁X v)
  have hBo : ∀ u ∈ orth S X, B u = 0 := fun u hu => by rw [hBapp, hB₀o u hu, hB₁o u hu, add_zero]
  have hBB : ∀ v, B (B v) = 0 := fun v => hBo _ (hXo (hBX v))
  have hBiso : ∀ v v', S.hT (v + B v) (v' + B v') = S.hT v v' := fun v v' => by
    have expand : S.hT (v + B v) (v' + B v') = S.hT v v' + S.hT (B v) v' + S.hT v (B v') + S.hT (B v) (B v') := by
      simp only [map_add (f := _), LinearMap.add_apply]; ring
    have f1 : S.hT (B v) v' = S.hT (B₀ v) v' + (-(star c) * (S.hT (B₀ v) v' + S.hT v (B₀ v'))) := by
      rw [hBapp, map_add (f := _), LinearMap.add_apply, hB₁]
    have f2 : S.hT v (B v') = S.hT v (B₀ v') + (-c * (S.hT (B₀ v) v' + S.hT v (B₀ v'))) := by
      rw [hBapp, map_add (f := _), hsw S (B₁ v') v, hB₁, star_mul, star_neg, star_add, ← hsw S (B₀ v') v,
        ← hsw S v' (B₀ v), star_star]
      ring
    rw [expand, hXiso _ (hBX v) _ (hBX v'), f1, f2]
    linear_combination (-(S.hT (B₀ v) v' + S.hT v (B₀ v'))) * hc
  let n : S.V ≃ₗ[E] S.V := LinearEquiv.ofLinear (LinearMap.id + B) (LinearMap.id - B)
    (by ext v; simp [hBB]) (by ext v; simp [hBB])
  have hnapp : ∀ v, n v = v + B v := fun v => rfl
  have hniso : ∀ a b, S.hT (n a) (n b) = S.hT a b := fun a b => by rw [hnapp, hnapp, hBiso]
  have hnin : ∀ x ∈ Λ₃, n x ∈ Λ := fun x hx => by
    rw [hnapp, hBapp, ← add_assoc]
    refine Λ.add_mem (by rw [hB₀ x hx]; exact hδΛ ⟨x, hx⟩) ((hM _ (hXo (hB₁X x))).1 ?_)
    refine (hSD₃ _).2 fun y hy => ?_
    have hσ : IsIntegral ℤ (S.hT (B₀ x) y + S.hT x (B₀ y)) := by
      have h1 : IsIntegral ℤ (S.hT (x + B₀ x) (y + B₀ y)) := by
        rw [hB₀ x hx, hB₀ y hy]; exact sd_int hSD (hδΛ ⟨y, hy⟩) (hδΛ ⟨x, hx⟩)
      have h2 : IsIntegral ℤ (S.hT x y) := sd_int hSD₃ hy hx
      have e : S.hT (B₀ x) y + S.hT x (B₀ y) = S.hT (x + B₀ x) (y + B₀ y) - S.hT x y := by
        rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hXiso _ (hB₀X x) _ (hB₀X y)]
        ring
      rw [e]; exact h1.sub h2
    rw [hsw S (B₁ x) y, hB₁, star_mul, star_neg, star_star]
    exact (isInt_star hσ).mul hcI.neg
  refine ⟨n, hniso, fun x hx => by rw [hnapp, hBo x hx, add_zero], ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hnin y hy
  · intro hx
    refine ⟨n.symm x, (hSD₃ _).2 fun y hy => ?_, n.apply_symm_apply x⟩
    rw [← hniso y (n.symm x), n.apply_symm_apply]
    exact sd_int hSD hx (hnin y hy)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocFramePrimJoint
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting
open scoped TensorProduct Classical

namespace ChkLocFramePrim

theorem primX_of (hS : PI.LocFramePrim.Statement) {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (w : D.what₂.Word)
    (Lb : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E))
    (hFG : X.B.I.L.FG)
    (hsplit : X.B.I.L =
      PI.LocFramePrim.latSpan (fun a : Fin D.R.rS => PI.LocFramePrim.ddE X.B.I.F ^ (-((D.R.rS : ℤ) - (a : ℕ))))
          (frameOf X w).e ⊔ Lb ⊔
        PI.LocFramePrim.latSpan (fun a : Fin D.R.rS => (PI.LocFramePrim.ddE X.B.I.F ^ (-((D.R.rS : ℤ) - (a : ℕ))))⁻¹)
          (frameOf X w).f)
    (hind : LinearIndependent X.B.I.E (Fin.append (frameOf X w).e (frameOf X w).f))
    (hdir : ∀ y ∈ Lb, y ∈ Submodule.span X.B.I.E (Set.range (frameOf X w).e ∪ Set.range (frameOf X w).f) → y = 0)
    (hz : (frameOf X w).z ∈ Lb)
    (hzp : ∀ c : X.B.I.E, c • (frameOf X w).z ∈ Lb → ∃ o : 𝓞 X.B.I.E, (o : X.B.I.E) = c) :
    PrimX X w := fun v =>
  hS X.B.I.F X.B.I.E v X.B.I.n D.R.rS X.B.I.L Lb (frameOf X w).e (frameOf X w).f (frameOf X w).z
    hFG hsplit hind hdir hz hzp

end ChkLocFramePrim
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSDLoc
section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX.SDL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

def swp : E ⊗[F] Fv F v ≃ₐ[F] Fv F v ⊗[F] E := Algebra.TensorProduct.comm F E (Fv F v)

theorem swp_tmul (a : E) (c : Fv F v) : swp v (a ⊗ₜ[F] c) = c ⊗ₜ[F] a := rfl

def swVv (w : Fin n → E ⊗[F] Fv F v) : Fin n → Fv F v ⊗[F] E := fun i => swp v (w i)

theorem swVv_injective : Function.Injective (swVv (E := E) v (n := n)) := fun _ _ h =>
  funext fun i => (swp v).injective (congrFun h i)

theorem swVv_surjective : Function.Surjective (swVv (E := E) v (n := n)) := fun w =>
  ⟨fun i => (swp v).symm (w i), funext fun i => (swp v).apply_symm_apply (w i)⟩

theorem swVv_incl (x : Fin n → E) :
    swVv v (fun i => PI.SelfDualLoc.inclE (F := F) (Fv F v) (x i)) = ratV (F := F) (Fv F v) x := by
  funext i
  simp [swVv, swp, PI.SelfDualLoc.inclE, ratV, inclR, Algebra.TensorProduct.comm_tmul]

theorem sig_swap (σ : E →ₐ[F] E) (t : E ⊗[F] Fv F v) :
    sigR (Fv F v) σ (swp v t) = swp v (PI.SelfDualLoc.sigR σ (Fv F v) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => simp [sigR, PI.SelfDualLoc.sigR, swp, Algebra.TensorProduct.comm_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem incl_swap (e : E) : swp v (PI.SelfDualLoc.inclE (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) e := by
  simp [swp, PI.SelfDualLoc.inclE, inclR, Algebra.TensorProduct.comm_tmul]

theorem hR_swap (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (z y : Fin n → E ⊗[F] Fv F v) :
    hR (Fv F v) σ J (swVv v z) (swVv v y) =
      swp v (PI.SelfDualLoc.hform (PI.SelfDualLoc.sigR σ (Fv F v)) (J.map (PI.SelfDualLoc.inclE (F := F) (Fv F v))) z y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, PI.SelfDualLoc.hform, map_sum, map_mul, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [swVv, sig_swap, incl_swap]

section Rings

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

abbrev Sv : Subring (E ⊗[F] Fv F v) :=
  PI.SelfDualLoc.tensInt (F := F) (Fv F v) (PI.SelfDualLoc.intOE E) (v.adicCompletionIntegers F).toSubring

theorem oev_gen (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨a, trivial, rfl⟩

theorem oev_mul {s t : Fv F v ⊗[F] E} (hs : s ∈ OEv (E := E) v) (ht : t ∈ OEv (E := E) v) :
    s * t ∈ OEv (E := E) v := by
  unfold OEv at hs ht ⊢
  rw [SetLike.mem_coe] at hs ht ⊢
  induction hs using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    induction ht using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨b, -, rfl⟩ := hb
      exact Submodule.subset_span ⟨a * b, trivial, by simp [map_mul]⟩
    | zero => simp
    | add y z _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h =>
      show _ * ((c : Fv F v) • y) ∈ _
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c h
  | zero => simp
  | add x z _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    show ((c : Fv F v) • x) * t ∈ _
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c h

theorem oev_alg (c : v.adicCompletionIntegers F) : ((c : Fv F v) ⊗ₜ[F] (1 : E)) ∈ OEv (E := E) v := by
  have h : ((c : Fv F v) ⊗ₜ[F] (1 : E)) = c • inclR (F := F) (Fv F v) ((1 : 𝓞 E) : E) := by
    simp [inclR, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  rw [h]
  exact Submodule.smul_mem _ c (oev_gen v 1)

theorem swp_mem_oev {s : E ⊗[F] Fv F v} (hs : s ∈ Sv (E := E) v) : swp v s ∈ OEv (E := E) v := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨a, ⟨b, rfl⟩⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩
    · exact oev_gen v b
    · exact oev_alg v ⟨c, hc⟩
  | zero => rw [map_zero]; exact zero_mem (Submodule.span _ _)
  | one => rw [map_one]; simpa using oev_gen v (E := E) 1
  | add x y _ _ hx hy => rw [map_add]; exact add_mem (S := Submodule _ _) hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem (S := Submodule _ _) hx
  | mul x y _ _ hx hy => rw [map_mul]; exact oev_mul v hx hy

theorem oev_swp {t : Fv F v ⊗[F] E} (ht : t ∈ OEv (E := E) v) : ∃ s ∈ Sv (E := E) v, swp v s = t := by
  unfold OEv at ht
  rw [SetLike.mem_coe] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, rfl⟩ := hx
    refine ⟨(a : E) ⊗ₜ[F] (1 : Fv F v), Subring.subset_closure (Or.inl ⟨⟨(a : E), ⟨a, rfl⟩⟩, rfl⟩), ?_⟩
    rfl
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', rfl⟩ := hy
    exact ⟨s + s', add_mem hs hs', map_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    refine ⟨((1 : E) ⊗ₜ[F] (c : Fv F v)) * s,
      mul_mem (Subring.subset_closure (Or.inr ⟨c, rfl⟩)) hs, ?_⟩
    rw [map_mul, swp_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl

end Rings

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Lb : Submodule (𝓞 E) (Fin n → E))

theorem oev_smul_lat {t : Fv F v ⊗[F] E} (ht : t ∈ OEv (E := E) v) {w : Fin n → Fv F v ⊗[F] E}
    (hw : w ∈ latLoc v (Lb : Set (Fin n → E))) : (fun i => t * w i) ∈ latLoc v (Lb : Set (Fin n → E)) := by
  unfold OEv at ht
  rw [SetLike.mem_coe] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, rfl⟩ := hx
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine Submodule.subset_span ⟨a • x, Lb.smul_mem a hx, ?_⟩
      funext i
      simp [ratV, map_mul, Pi.smul_apply, Algebra.smul_def]
    | zero =>
      convert zero_mem (latLoc v (Lb : Set (Fin n → E))) using 1
      funext i; simp
    | add y z _ _ hy hz =>
      have e : (fun i => inclR (F := F) (Fv F v) (a : E) * (y + z) i) =
          (fun i => inclR (F := F) (Fv F v) (a : E) * y i) + (fun i => inclR (F := F) (Fv F v) (a : E) * z i) := by
        funext i; simp [mul_add]
      rw [e]; exact add_mem hy hz
    | smul c y _ hy =>
      have e : (fun i => inclR (F := F) (Fv F v) (a : E) * (c • y) i) =
          c • (fun i => inclR (F := F) (Fv F v) (a : E) * y i) := by
        funext i; simp [mul_smul_comm]
      rw [e]; exact Submodule.smul_mem _ c hy
  | zero =>
    convert zero_mem (latLoc v (Lb : Set (Fin n → E))) using 1
    funext i; simp
  | add x y _ _ hx hy =>
    have e : (fun i => (x + y) * w i) = (fun i => x * w i) + (fun i => y * w i) := by funext i; simp [add_mul]
    rw [e]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : (fun i => (c • x) * w i) = c • (fun i => x * w i) := by funext i; simp [smul_mul_assoc]
    rw [e]; exact Submodule.smul_mem _ c hx

theorem swVv_mem_latLoc {z : Fin n → E ⊗[F] Fv F v}
    (hz : z ∈ PI.SelfDualLoc.latS (F := F) (Fv F v) (Sv (E := E) v) Lb) :
    swVv v z ∈ latLoc v (Lb : Set (Fin n → E)) := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [swVv_incl]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : swVv v (0 : Fin n → E ⊗[F] Fv F v) = 0 := by funext i; simp [swVv]
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : swVv v (x + y) = swVv v x + swVv v y := by funext i; simp [swVv]
    rw [this]; exact add_mem hx hy
  | smul s x _ hx =>
    have : swVv v (s • x) = fun i => swp v (s : E ⊗[F] Fv F v) * swVv v x i := by
      funext i; simp [swVv, Submodule.coe_smul_of_tower, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]
    exact oev_smul_lat v Lb (swp_mem_oev v s.2) hx

theorem latLoc_swVv {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc v (Lb : Set (Fin n → E))) :
    ∃ z ∈ PI.SelfDualLoc.latS (F := F) (Fv F v) (Sv (E := E) v) Lb, swVv v z = w := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩, swVv_incl v x⟩
  | zero => exact ⟨0, zero_mem _, by funext i; simp [swVv]⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    exact ⟨z + z', add_mem hz hz', by funext i; simp [swVv]⟩
  | smul c x _ hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    have hc : ((1 : E) ⊗ₜ[F] (c : Fv F v)) ∈ Sv (E := E) v := Subring.subset_closure (Or.inr ⟨c, rfl⟩)
    refine ⟨(⟨_, hc⟩ : Sv (E := E) v) • z, Submodule.smul_mem _ _ hz, ?_⟩
    funext i
    simp only [swVv, Pi.smul_apply]
    rw [Subring.smul_def, smul_eq_mul, map_mul, swp_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl

theorem isSDLoc_of (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hfg : Lb.FG)
    (hint : ∀ x ∈ Lb, ∀ y ∈ Lb, PI.SelfDualLoc.hform (σ : E →+* E) J x y ∈ PI.SelfDualLoc.intOE E)
    (hdual : ∀ y : Fin n → E, (∀ x ∈ Lb, PI.SelfDualLoc.hform (σ : E →+* E) J x y ∈ PI.SelfDualLoc.intOE E) → y ∈ Lb) :
    IsSDLoc σ J v (Lb : Set (Fin n → E)) := by
  have hT : ((1 : ℕ) : 𝓞 F) ∉ v.asIdeal := by
    rw [Nat.cast_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have key := self_dual_local F E n σ J v Lb 1 (Module.Finite.iff_fg.2 hfg) hint
    (fun y hy => by simpa using hdual y hy) hT
  intro y'
  obtain ⟨y, rfl⟩ := swVv_surjective (E := E) v y'
  have hlat : swVv v y ∈ latLoc v (Lb : Set (Fin n → E)) ↔
      y ∈ PI.SelfDualLoc.latS (F := F) (Fv F v) (Sv (E := E) v) Lb := by
    constructor
    · intro h
      obtain ⟨z, hz, e⟩ := latLoc_swVv v Lb h
      rwa [← swVv_injective v e]
    · exact swVv_mem_latLoc v Lb
  rw [hlat, key]
  constructor
  · intro h x' hx'
    obtain ⟨z, hz, rfl⟩ := latLoc_swVv v Lb hx'
    rw [hR_swap]
    exact swp_mem_oev v (h z hz)
  · intro h z hz
    have h1 := h (swVv v z) (swVv_mem_latLoc v Lb hz)
    rw [hR_swap] at h1
    obtain ⟨s, hs, e⟩ := oev_swp v h1
    rwa [← (swp v).injective e]

end Lat

theorem sdLocX_holds {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : PlX X) :
    IsSDLoc X.B.I.cm.sig X.B.I.J v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
  isSDLoc_of v X.B.I.L X.B.I.cm.sig X.B.I.J X.B.I.L_fg
    (fun x hx y hy => (X.B.I.L_dual y).1 hy x hx) (fun y h => (X.B.I.L_dual y).2 h)

end Formalism.L2.SG.Pf.MassDataX.SDL
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvCut
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)

def AlConvC : Prop :=
  Multipliable (fun v : OrdX X => alX X u u' v.1) ∧ 0 < ∏' v : OrdX X, alX X u u' v.1

end Formalism.L2.SG.Pf.ProdConvCut

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.ProdConvCut

end Formalism.L2.SG.Pf
end
end

