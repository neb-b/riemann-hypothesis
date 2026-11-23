module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

@[expose] public section

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Const

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem Rder_const (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ) :
    Rder θ V τ Z (fun _ => c) = fun _ => 0 := by
  funext g
  unfold Rder
  simp

theorem RderC_const (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ) :
    RderC θ V τ Z (fun _ => c) = fun _ => 0 := by
  funext g
  unfold RderC
  simp [Rder_const]

theorem foldr_const (l : List ((GA D V → ℂ) → (GA D V → ℂ)))
    (hl : ∀ f ∈ l, ∀ c : ℂ, ∃ c' : ℂ, f (fun _ => c) = fun _ => c') (c : ℂ) :
    ∃ c' : ℂ, l.foldr (fun f acc => f acc) (fun _ => c) = fun _ => c' := by
  induction l with
  | nil => exact ⟨c, rfl⟩
  | cons f l ih =>
    obtain ⟨c1, h1⟩ := ih (fun g hg => hl g (by simp [hg]))
    obtain ⟨c2, h2⟩ := hl f (by simp) c1
    exact ⟨c2, by simp only [List.foldr_cons, h1, h2]⟩

theorem gelf_const (τ : D.what₂.Tau) (k : ℕ) (c : ℂ) : ∃ c' : ℂ, gelf θ V τ k (fun _ => c) = fun _ => c' := by
  unfold gelf
  apply Finset.sum_induction _ (fun F => ∃ c', F = fun _ => c')
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, rfl⟩
  · exact ⟨0, rfl⟩
  · intro idx _
    apply foldr_const
    intro f hf c0
    rw [List.mem_ofFn] at hf
    obtain ⟨a, rfl⟩ := hf
    exact ⟨0, RderC_const θ V τ _ c0⟩

theorem foldrRder_const (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (c : ℂ) :
    ∃ c' : ℂ, l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun _ => c) = fun _ => c' := by
  induction l with
  | nil => exact ⟨c, rfl⟩
  | cons p l ih =>
    obtain ⟨c1, h1⟩ := ih
    exact ⟨0, by simp only [List.foldr_cons, h1, Rder_const]⟩

theorem isAutFunSm_const (c : ℂ) : IsAutFunSm θ V (fun _ => c) := by
  refine ⟨⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const⟩,
    fun _ _ _ _ _ => contDiff_const, ?_, ?_⟩
  ·
    refine ⟨Submodule.span ℂ {fun _ => (1 : ℂ)}, FiniteDimensional.span_singleton ℂ _, ?_, ?_⟩
    · exact Submodule.mem_span_singleton.2 ⟨c, by funext g; simp⟩
    · intro τ k f hf
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
      have e : (a • fun _ : GA D V => (1 : ℂ)) = fun _ => a := by funext g; simp
      obtain ⟨c', hc'⟩ := gelf_const θ V τ k a
      rw [e, hc']
      exact Submodule.mem_span_singleton.2 ⟨c', by funext g; simp⟩
  ·
    refine ⟨0, fun l _ x => ?_⟩
    obtain ⟨c', hc'⟩ := foldrRder_const θ V l c
    exact ⟨‖c'‖, fun g _ => by rw [hc', pow_zero, mul_one]⟩

end Const

theorem VolTieG.volTie (h : VolTieG D) : Formalism.MainNotions.StandardLattice.VolTie D := by
  unfold VolTieG at h
  unfold Formalism.MainNotions.StandardLattice.VolTie
  intro W P Q hW hsig
  have e1 : (fun ρ => (W.sig (tauE D ρ)).1) = fun _ => P := by
    funext ρ
    rw [hsig]
  have e2 : (fun ρ => (W.sig (tauE D ρ)).2) = fun _ => Q := by
    funext ρ
    rw [hsig]
  have h' := h W hW
  rw [e1, e2] at h'
  exact h'

end Formalism.L2.Theta

end
end

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Matrix
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {R : Type*} [CommRing R] (c : R →+* R) {n m : ℕ}

theorem sum_eq_trace (J : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R) (x y : Matrix (Fin n) (Fin m) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, c (x i j) * J k i * K j l * y k l = ((x.map c)ᵀ * Jᵀ * y * Kᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem inv_hom (hc : ∀ a, c (c a) = a) (J g : Matrix (Fin n) (Fin n) R) (K h : Matrix (Fin m) (Fin m) R)
    (hg : (g.map c)ᵀ * J * g = J) (hh : (h.map c)ᵀ * K * h = K) (x y : Matrix (Fin n) (Fin m) R) :
    (((g.map c * x * hᵀ).map c)ᵀ * Jᵀ * (g.map c * y * hᵀ) * Kᵀ).trace = ((x.map c)ᵀ * Jᵀ * y * Kᵀ).trace := by
  have hgg : (g.map c).map c = g := by
    ext i j
    simp [hc]
  have e1 : (g.map c * x * hᵀ).map c = g * x.map c * (h.map c)ᵀ := by
    rw [Matrix.map_mul, Matrix.map_mul, hgg, Matrix.transpose_map]
  have h1 : gᵀ * Jᵀ * g.map c = Jᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hg
  have hg2 : ∀ M : Matrix (Fin n) (Fin m) R, gᵀ * (Jᵀ * (g.map c * M)) = Jᵀ * M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1]
  have hh1 : hᵀ * Kᵀ * h.map c = Kᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hh
  have hh2 : hᵀ * (Kᵀ * h.map c) = Kᵀ := by
    rw [← Matrix.mul_assoc, hh1]
  rw [e1]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, hg2]
  conv_lhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hh2]

theorem inv_hom' (hc : ∀ a, c (c a) = a) (J g : Matrix (Fin n) (Fin n) R) (K h : Matrix (Fin m) (Fin m) R)
    (hg : (g.map c)ᵀ * J * g = J) (hh : (h.map c)ᵀ * K * h = K) (x y : Matrix (Fin n) (Fin m) R) :
    (((g * x * (h.map c)ᵀ).map c)ᵀ * J * (g * y * (h.map c)ᵀ) * K).trace = ((x.map c)ᵀ * J * y * K).trace := by
  have hhh : (h.map c).map c = h := by
    ext i j
    simp [hc]
  have e1 : (g * x * (h.map c)ᵀ).map c = g.map c * x.map c * hᵀ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hhh]
  have hg2 : ∀ M : Matrix (Fin n) (Fin m) R, (g.map c)ᵀ * (J * (g * M)) = J * M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg]
  have hh2 : (h.map c)ᵀ * (K * h) = K := by
    rw [← Matrix.mul_assoc, hh]
  rw [e1]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, hg2]
  conv_lhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hh2]

theorem idempotent_det_conj_identity (e : R) (h1 : e * e = e) (h2 : e * c e = 0) (g : Matrix (Fin n) (Fin n) R)
    (hs : ∀ i j, (e + c e) * (g - 1) i j = (g - 1) i j) (hd : c g.det * g.det = 1) :
    e * g.det + (1 - e) = g.det * c (e * g.det + (1 - e)) := by
  have h3 : c e * c e = c e := by rw [← map_mul, h1]
  have hf : (1 - (e + c e)) * (1 - (e + c e)) = 1 - (e + c e) := by
    linear_combination h1 + 2 * h2 + h3
  have hp : ∀ k : ℕ, (1 - (e + c e)) ^ (k + 1) = 1 - (e + c e) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, hf]
  have key : (1 - (e + c e)) * g.det = 1 - (e + c e) := by
    have hM : (1 - (e + c e)) • g = (1 - (e + c e)) • (1 : Matrix (Fin n) (Fin n) R) := by
      ext i j
      have := hs i j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply] at this ⊢
      linear_combination (-1 : R) * this
    have hd' := congrArg Matrix.det hM
    rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hd'
    cases n with
    | zero => rw [Matrix.det_isEmpty, mul_one]
    | succ k => rw [hp k] at hd'; exact hd'
  simp only [map_add (f := _), map_mul, map_sub, map_one]
  linear_combination -key - c e * hd

end Generic

variable {D : D7}

theorem cA_cA (a : AE D) : cA D (cA D a) = a := by
  have hs : ∀ x : D.host.E, D.sp.cm.sig (D.sp.cm.sig x) = x := by
    intro x
    unfold Formalism.BasicNotions.CMData.sig
    exact star_star x
  unfold cA sigR
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.map_tmul, hs]
  | add x y hx hy =>
    simp only [map_add (f := _)] at *
    rw [hx, hy]

theorem mt_rel (V : HSp D) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := by
  have hg := g.2
  unfold HR at hg
  simp only [UG.UJ, JR] at hg
  exact hg

theorem hHom_actHom (V W : HSp D) (g : GA D V) (h : GA D W) (x y : WA V W) :
    hHom V W (actHom V W g h x) (actHom V W g h y) = hHom V W x y := by
  unfold hHom actHom
  have hc : ∀ a, cA D (cA D a) = a := cA_cA
  split_ifs with hr
  · have e1 := sum_eq_trace (cA D) ((HSpace.gram V).map (incA D)) ((HSpace.gram W).map (incA D))
      (cM (mt V g) * x * (mt W h)ᵀ) (cM (mt V g) * y * (mt W h)ᵀ)
    have e2 := sum_eq_trace (cA D) ((HSpace.gram V).map (incA D)) ((HSpace.gram W).map (incA D)) x y
    simp only [Matrix.map_apply] at e1 e2
    rw [e1, e2]
    exact inv_hom (cA D) hc _ _ _ _ (mt_rel V g) (mt_rel W h) x y
  · have e1 := sum_eq_trace (cA D) ((HSpace.gram V).map (incA D))ᵀ ((HSpace.gram W).map (incA D))ᵀ
      (mt V g * x * (cM (mt W h))ᵀ) (mt V g * y * (cM (mt W h))ᵀ)
    have e2 := sum_eq_trace (cA D) ((HSpace.gram V).map (incA D))ᵀ ((HSpace.gram W).map (incA D))ᵀ x y
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.transpose_transpose] at e1 e2
    rw [e1, e2]
    exact inv_hom' (cA D) hc _ _ _ _ (mt_rel V g) (mt_rel W h) x y

theorem sympl_actHom (V W : HSp D) (g : GA D V) (h : GA D W) (x y : WA V W) :
    sympl V W (actHom V W g h x) (actHom V W g h y) = sympl V W x y := by
  unfold sympl
  rw [hHom_actHom]

theorem hHom_transpose (V W : HSp D) (hne : V.rank ≠ W.rank) (x y : WA V W) :
    hHom W V x.transpose y.transpose = hHom V W x y := by
  unfold hHom
  simp only [Matrix.transpose_apply]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · rw [if_neg (show ¬ W.rank ≤ V.rank by omega), if_pos (show V.rank ≤ W.rank by omega)]
    have e1 := sum_eq_trace (cA D) ((HSpace.gram W).map (incA D))ᵀ ((HSpace.gram V).map (incA D))ᵀ xᵀ yᵀ
    have e2 := sum_eq_trace (cA D) ((HSpace.gram V).map (incA D)) ((HSpace.gram W).map (incA D)) x y
    simp only [Matrix.transpose_apply, Matrix.map_apply] at e1 e2
    rw [e1, e2, ← Matrix.trace_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map, Matrix.mul_assoc]
    conv_rhs => rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  · rw [if_pos (show W.rank ≤ V.rank by omega), if_neg (show ¬ V.rank ≤ W.rank by omega)]
    have e1 := sum_eq_trace (cA D) ((HSpace.gram W).map (incA D)) ((HSpace.gram V).map (incA D)) xᵀ yᵀ
    have e2 := sum_eq_trace (cA D) ((HSpace.gram V).map (incA D))ᵀ ((HSpace.gram W).map (incA D))ᵀ x y
    simp only [Matrix.transpose_apply, Matrix.map_apply] at e1 e2
    rw [e1, e2, ← Matrix.trace_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map, Matrix.mul_assoc]
    conv_rhs => rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]

theorem actHom_swap (V W : HSp D) (hne : V.rank ≠ W.rank) (g : GA D V) (h : GA D W) (x : WA V W) :
    actHom W V h g x.transpose = (actHom V W g h x).transpose := by
  unfold actHom
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · rw [if_neg (show ¬ W.rank ≤ V.rank by omega), if_pos (show V.rank ≤ W.rank by omega)]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  · rw [if_pos (show W.rank ≤ V.rank by omega), if_neg (show ¬ V.rank ≤ W.rank by omega)]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem splitFac_swap (V W : HSp D) (hne : V.rank ≠ W.rank) (c c' : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) :
    splitFac W V c' c y x = splitFac V W c c' x y := by
  unfold splitFac
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · rw [if_neg (show ¬ W.rank ≤ V.rank by omega), if_pos (show V.rank ≤ W.rank by omega), mul_comm]
  · rw [if_pos (show W.rank ≤ V.rank by omega), if_neg (show ¬ V.rank ≤ W.rank by omega), mul_comm]

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  have hrow : ∀ i, ∑ j, V.gram i j * v j = 0 := fun i => by
    have := congrFun hJv i
    simpa [Matrix.mulVec, dotProduct] using this
  have hb : V.hT.flip (∑ j, v j • V.frame j) = 0 := by
    refine V.frame.ext fun i => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.flip_apply, LinearMap.zero_apply, map_sum, ← hrow i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
    exact mul_comm _ _
  have hy : ∀ x, V.hT x (∑ j, v j • V.frame j) = 0 := fun x => by
    have := LinearMap.congr_fun hb x
    rwa [LinearMap.flip_apply, LinearMap.zero_apply] at this
  have h0 := V.nondeg.2 _ hy
  funext i
  exact Fintype.linearIndependent_iff.mp V.frame.linearIndependent v h0 i

theorem det_conj_mul (V : HSp D) (g : GA D V) : cA D (mt V g).det * (mt V g).det = 1 := by
  have h := congrArg Matrix.det (mt_rel V g)
  have hd1 : ((mt V g).map (cA D)).det = cA D (mt V g).det := (RingHom.map_det (cA D) (mt V g)).symm
  have hd2 : (V.gram.map (incA D)).det = incA D V.gram.det := (RingHom.map_det (incA D) V.gram).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hd1, hd2] at h
  have hu : IsUnit (incA D V.gram.det) := (IsUnit.mk0 _ (gram_det_ne V)).map (incA D)
  apply hu.mul_left_cancel
  rw [mul_one]
  calc incA D V.gram.det * (cA D (mt V g).det * (mt V g).det)
      = cA D (mt V g).det * incA D V.gram.det * (mt V g).det := by ring
    _ = incA D V.gram.det := h

theorem isDetAt_root {e : AE D} (he : IsSplitIdem D e) (V : HSp D) (g : GA D V) (hs : SuppAt e V g) (x : (AE D)ˣ)
    (hx : IsDetAt e V g x) : IsDetRoot V g x := by
  unfold IsDetRoot
  unfold IsDetAt at hx
  unfold SuppAt at hs
  unfold IsSplitIdem at he
  rw [hx]
  exact idempotent_det_conj_identity (cA D) e he.1 he.2.1 (mt V g) hs (det_conj_mul V g)

variable {X : ThetaX D} {T : ThetaTied D X}

end Formalism.L2.Theta

end
end

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ratV {n : ℕ} (x : Fin n → D.host.E) : Fin n → AE D := fun i => incA D (x i)

def subOne (B : HSp D) (g : GA D B) : Matrix (Fin B.rank) (Fin B.rank) (AE D) :=
  ((matHom B g).1 : Matrix (Fin B.rank) (Fin B.rank) (AE D)) - 1

def NFlag (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) : Subgroup (GA D B) :=
  Subgroup.closure {g |
    (∀ i : Fin ρ, ∃ a : Fin ρ → AE D, (∀ j, i ≤ j → a j = 0) ∧
      (subOne B g).mulVec (ratV fun k => e k i) = (e.map (incA D)).mulVec a) ∧
    ∀ x : Fin B.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * B.gram).mulVec x = 0 →
      ∃ a : Fin ρ → AE D, (subOne B g).mulVec (ratV x) = (e.map (incA D)).mulVec a}

def NFlagQ (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) : Subgroup (NFlag B e) :=
  (GQ B).subgroupOf (NFlag B e)

structure BesDat (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) where
  ρ : ℕ
  codim : A.rank + 2 * ρ + 1 = B.rank

  e : Matrix (Fin B.rank) (Fin ρ) D.host.E
  e_iso : IsIsoSub B e
  e_perp : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram * e = 0

  z : Fin B.rank → D.host.E
  z_perpA : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram).mulVec z = 0
  z_perpE : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * B.gram).mulVec z = 0
  z_ne : Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) B.gram z z ≠ 0

  c : Fin ρ → D.host.E
  c_ne : ∀ i, c i ≠ 0

  y : GfC B

def IsBesVal (ψ : AddChar (AF D.host.F) ℂ) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (n : GA D B)
    (v : ℂ) : Prop :=
  ∃ (a : Fin d.ρ → Fin d.ρ → AE D) (b : Fin d.ρ → AE D),
    (∀ i, (subOne B n).mulVec (ratV fun k => d.e k i) = (d.e.map (incA D)).mulVec (a i)) ∧
    (subOne B n).mulVec (ratV d.z) = (d.e.map (incA D)).mulVec b ∧
    v = ψ (Algebra.trace (AF D.host.F) (AE D)
      ((∑ i : Fin d.ρ, ∑ j : Fin d.ρ, if j.1 = i.1 + 1 then incA D (d.c i) * a j i else 0) +
        ∑ i : Fin d.ρ, if i.1 + 1 = d.ρ then incA D (d.c i) * b i else 0))


open Classical in
def besChar (ψ : AddChar (AF D.host.F) ℂ) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (n : GA D B) : ℂ :=
  if h : ∃ v, IsBesVal ψ d n v then h.choose else 1

def IsAniso (A : HSp D) : Prop := ∀ (r : ℕ) (C : Matrix (Fin A.rank) (Fin r) D.host.E), ¬ IsIsoFrame A C

structure BesselTied (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) where

  dat : ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), Odd (B.rank - A.rank) → X.Pos A B ι → BesDat A B ι

  dat_y : ∀ A B ι h p, ((dat A B ι h p).y : GA D B) = 1

  besC : ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), X.Pos A B ι → ℝ
  besC_pos : ∀ A B ι p, 0 < besC A B ι p

  bper : ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (ho : Odd (B.rank - A.rank)), A.rank ≤ B.rank → A.SigOK →
    HSpace.IsIsomEmb A B ι → ∀ (p : X.Pos A B ι), (∃ u, HEq p (X.posSym u)) → ∀ (sF : X.FJd A B ι),
    ∀ μ 𝓕, IsVolPair D A μ 𝓕 →
    ∀ (μN : Measure (NFlag B (dat A B ι ho p).e)) (𝓕N : Set (NFlag B (dat A B ι ho p).e)), μN.IsHaarMeasure →
      IsFundamentalDomain (NFlagQ B (dat A B ι ho p).e) 𝓕N μN → μN 𝓕N = 1 →
    ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) →
    ∀ (φ : X.AF A) (F : X.cusp B), IsAniso A ∨ φ ∈ X.cusp A →
      X.Bper A B ι p sF φ F = ((besC A B ι p * T.petC A : ℝ) : ℂ) *
        ∫ h in 𝓕, ∫ n in 𝓕N, star (T.ev A φ h) *
          T.ev B (F : X.AF B) ((n : GA D B) * s h * ((dat A B ι ho p).y : GA D B)) *
          star (besChar Wl.ψ (dat A B ι ho p) (n : GA D B)) ∂μN ∂μ

  besC_one : ∀ A B ι p, besC A B ι p = 1

end Formalism.L2.Theta

end
end

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rep

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))

def SmoothVec (w : H) : Prop :=
  ∀ (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, Xs i ∈ Lie) →
    ContDiff ℝ ∞ fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) w

def dRep (X : Matrix (Fin n) (Fin n) ℂ) (w : H) : H := deriv (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) 0

def Sobolev₂ (ℓ : H →ₗ[ℂ] ℂ) : Prop :=
  ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ Lie) ∧
    ∀ w, SmoothVec Lie σ w → ‖ℓ w‖ ≤ C * (S.map fun l => ‖l.foldr (dRep σ) w‖).sum

end Rep

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

def IsTypeAt (τ : D.what₂.Tau) (S : SPar) (φ : GA D V → ℂ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
    (P : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsEnum S lam ε ∧ IsDS ε lam σ ∧ IsUnit P ∧ Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ ∧
    ∀ x, ∃ v : ℕ → H, (∀ i, SmoothVec (lieAt V τ) (fun g => σ (P * g * P⁻¹)) (v i)) ∧
      ∃ ℓ : ℕ → (H →ₗ[ℂ] ℂ), (∀ i, Sobolev₂ (lieAt V τ) (fun g => σ (P * g * P⁻¹)) (ℓ i)) ∧

        (∃ (S : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℕ → ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieAt V τ) ∧
          (∀ i w, SmoothVec (lieAt V τ) (fun g => σ (P * g * P⁻¹)) w →
            ‖ℓ i w‖ ≤ C i * (S.map fun l => ‖l.foldr (dRep (fun g => σ (P * g * P⁻¹))) w‖).sum) ∧
          (∀ S' : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ l ∈ S', ∀ X ∈ l, X ∈ lieAt V τ) →
            Summable (fun i => C i * (S'.map fun l => ‖l.foldr (dRep (fun g => σ (P * g * P⁻¹))) (v i)‖).sum)) ∧

          (∃ B : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ, Continuous B ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w,
            SmoothVec (lieAt V τ) (fun g => σ (P * g * P⁻¹)) w →
            (S.map fun l => ‖l.foldr (dRep (fun g => σ (P * g * P⁻¹))) (σ (P * g * P⁻¹) w)‖).sum ≤
              B g * (S.map fun l => ‖l.foldr (dRep (fun g => σ (P * g * P⁻¹))) w‖).sum)) ∧
        ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), HasSum (fun i => ℓ i (σ (P * g * P⁻¹) (v i))) (φ (x * atTau θ V τ g))

def TypTied {X : ThetaX D} (T : ThetaTied D X) : Prop :=
  AllSome (IsInfFam (D := D)) fun θ => ∀ V : HSp D, V.SigOK → ∀ P : D.what₂.Tau → SPar,
    (∀ τ, GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 (P τ)) →
    (∀ τ, SParGap V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 (P τ)) →
    ∀ F, F ∈ X.typ V P ↔ ∀ τ, IsTypeAt θ V τ (P τ) (T.ev V F)

end Formalism.L2.Theta

end
end

