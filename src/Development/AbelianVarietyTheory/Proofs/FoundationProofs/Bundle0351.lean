module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0348
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.AdmissibleTwistByDet

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlochKatoCocycleUnramifiedAndGreenbergOrdinary
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory.Ord2

theorem bk_unr_gr : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → Unr W z ∧ Gr W A z := by
  intro hP l _ Ω _ _ _ e S A W hN z hz hbk
  have hcol : ∀ s x, Loc.colRep W s x = mat W s *ᵥ x := fun s x => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨B, hB, x, hx⟩ := hbk.away w hw
    exact ⟨B, hB, x, fun s hs => by rw [hx s hs, hcol]⟩
  obtain ⟨ι, hιc, hιD, hιS, hιI, hιcyc, hιZ⟩ := GlobalTheory.T.crystallineClass_restrict_decompositionGroup l Ω W A hN.atL z hz hbk
  have hup : ∀ σ, mat W (ι σ) 1 0 = 0 := fun σ => hN.upper _ (hιD σ)
  let k0 : GQ l →* Qbar l :=
    { toFun := fun σ => mat W (ι σ) 1 1
      map_one' := by simp [mat]
      map_mul' := fun σ τ => by
        have h := hup σ
        simp only [mat] at h
        simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h, zero_mul, zero_add] }
  let κ : GQ l →* (Qbar l)ˣ := k0.toHomUnits
  have hκ : ∀ σ, (κ σ : Qbar l) = mat W (ι σ) 1 1 := fun σ => rfl
  have hκc : Continuous fun σ => (κ σ : Qbar l) :=
    ((Units.continuous_val.comp (hN.cont.comp hιc)).matrix_elem 1 1)
  let f : (Fin 2 → Qbar l) →ₗ[ℚ_[l]] Qbar l := LinearMap.proj (R := ℚ_[l]) (φ := fun _ : Fin 2 => Qbar l) 1
  have hf : ∀ σ x, f (((Loc.colRep W).comp ι) σ x) = Loc.chRep κ σ (f x) := fun σ x => by
    have h := hup σ
    simp only [mat] at h
    simp [f, Loc.chRep, hcol, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hκ, mat, h]
  have hc := Loc.z1fCoef (MonoidHom.id (GQ l)) _ _ f (continuous_apply 1) hf _ hιZ
  obtain ⟨c, hcO⟩ := hN.int
  obtain ⟨m, hm1, hm⟩ := hN.wt
  have hw : Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
    refine _root_.GlobalTheory.hasWeight_neg_of_pow_cyc_inertia l κ hκc e (2 * m) (by omega) fun σ hσ => ?_
    have hs := hιI σ hσ
    have h0 := hm _ hs
    have hd : (dt W (ι σ) : Qbar l) ^ 2 = 1 := by
      have := congrArg (fun u : G ℚ Ω →* (Qbar l)ˣ => ((u (ι σ) : (Qbar l)ˣ) : Qbar l)) hN.det2
      simpa using this
    have hdet : (dt W (ι σ) : Qbar l) = mat W (ι σ) 0 0 * mat W (ι σ) 1 1 := by
      have h := hup σ
      simp only [mat] at h
      simp [dt, Matrix.det_fin_two, mat, h]
    have hcy : (Loc.cycA l l (Qbar l) σ : Qbar l) = eps l (ι σ) := by
      simp only [Loc.cycA, eps, cycBar, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hιcyc, RingHom.coe_comp, Function.comp_apply]
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
      rfl
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_natCast, Units.val_one, hκ, hcy]
    rw [hdet] at hd
    calc (mat W (ι σ) 1 1 * eps l (ι σ) ^ e) ^ (2 * m) = (mat W (ι σ) 1 1) ^ (2 * m) * (eps l (ι σ) ^ (e * m)) ^ 2 := by ring
      _ = ((mat W (ι σ) 0 0 * mat W (ι σ) 1 1) ^ 2) ^ m := by rw [← h0]; ring
      _ = 1 := by rw [hd, one_pow]
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight hP l κ hκc c (fun σ => hcO _ 1 1) (-(e : ℤ)) (by have := hN.e_pos; omega) hw _ hc
  refine ⟨x, fun s hs => ?_⟩
  obtain ⟨σ, rfl⟩ := hιS s hs
  have := hx σ
  simpa [f, hκ] using this

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPrimePowTorsionSelmerClassesModPrimePowBound
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.TorsBound

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem natCast_ne_zero' : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

theorem norm_mul_pow_le_iff (k j : ℕ) (a : Qbar l) :
    ‖((l : ℕ) : Qbar l) ^ k * a‖ ≤ ‖((l : ℕ) : Qbar l) ^ (k + j)‖ ↔ ‖a‖ ≤ ‖((l : ℕ) : Qbar l) ^ j‖ := by
  rw [norm_mul, pow_add, norm_mul]
  have : 0 < ‖((l : ℕ) : Qbar l) ^ k‖ := norm_pos_iff.2 (pow_ne_zero _ natCast_ne_zero')
  exact mul_le_mul_iff_of_pos_left this

theorem cv_of_smul {k m : ℕ} {a b w w' : Fin 2 → Qbar l} (h : ((l : ℕ) : Qbar l) ^ k • (a - b) = w - w')
    (hw : Cv (k + m) w w') : Cv m a b := fun i => by
  have e := congrFun h i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
  have := hw i
  unfold Cg at this ⊢
  rw [← e] at this
  exact (norm_mul_pow_le_iff k m _).1 this

theorem cv_smul {k m : ℕ} {a b w w' : Fin 2 → Qbar l} (h : ((l : ℕ) : Qbar l) ^ k • (a - b) = w - w')
    (hab : Cv m a b) : Cv (k + m) w w' := fun i => by
  have e := congrFun h i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
  have := hab i
  unfold Cg at this ⊢
  rw [← e]
  exact (norm_mul_pow_le_iff k m _).2 this

theorem mem_of_mul (c : Coef l) (k : ℕ) {a : Qbar l} (ha : ((l : ℕ) : Qbar l) ^ k * a ∈ c.O) (hn : ‖a‖ ≤ 1) :
    a ∈ c.O :=
  mem_coefO_of_memE_norm_le_one l c a ⟨k, ha⟩ hn

theorem exists_cls (c : Coef l) (m : ℕ) : ∃ (T : Type) (_ : Fintype T) (cls : (Fin 2 → c.O) → T),
    ∀ x y, cls x = cls y → ∀ j, ‖((x j : c.O) : Qbar l) - (y j : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖ := by
  have hl0 : ((l : ℕ) : c.O) ^ m ≠ 0 := pow_ne_zero _ (by
    intro h
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    exact natCast_ne_zero' (by simpa using h'))
  haveI hfin := (UpperTheory.V.X.So.levFacts l c.O _ hl0 (c.O ⧸ Ideal.span {((l : ℕ) : c.O) ^ m})
    ⟨LinearEquiv.refl _ _⟩).1
  refine ⟨Fin 2 → c.O ⧸ Ideal.span {((l : ℕ) : c.O) ^ m}, Fintype.ofFinite _,
    fun x j => Ideal.Quotient.mk _ (x j), ?_⟩
  intro x y h j
  have h1 := congrFun h j
  simp only at h1
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h1
  obtain ⟨w, hw⟩ := h1
  have e : ((x j : c.O) : Qbar l) - (y j : Qbar l) = ((l : ℕ) : Qbar l) ^ m * (w : Qbar l) := by
    have := congrArg (fun z : c.O => (z : Qbar l)) hw
    simpa using this
  rw [e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem_coefO c w)

def cobd (V : R2 Ω l) (s : G ℚ Ω) : (Fin 2 → Qbar l) →ₗ[Qbar l] (Fin 2 → Qbar l) :=
  Matrix.mulVecLin (mat V s) - LinearMap.id

theorem cobd_apply (V : R2 Ω l) (s : G ℚ Ω) (y : Fin 2 → Qbar l) : cobd V s y = mat V s *ᵥ y - y := rfl

theorem cobd_mul (V : R2 Ω l) (s t : G ℚ Ω) (y : Fin 2 → Qbar l) :
    cobd V (s * t) y = cobd V s y + mat V s *ᵥ cobd V t y := by
  simp only [cobd_apply, mat_mul', ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
  abel

end GlobalTheory.Ord2.TorsBound

namespace GlobalTheory.Ord2.TorsBound

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def lift (V : R2 Ω l) (m k : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (x : Fin 2 → Qbar l) (s : G ℚ Ω) : Fin 2 → Qbar l :=
  (((l : ℕ) : Qbar l) ^ k)⁻¹ • (z s - cobd V s ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x))

theorem smul_lift (V : R2 Ω l) (m k : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (x : Fin 2 → Qbar l) (s : G ℚ Ω) :
    ((l : ℕ) : Qbar l) ^ k • lift V m k z x s = z s - cobd V s ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x) :=
  smul_inv_smul₀ (pow_ne_zero _ natCast_ne_zero') _

theorem smul_diff (V : R2 Ω l) (m : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (x : Fin 2 → Qbar l) (s : G ℚ Ω) :
    ((l : ℕ) : Qbar l) ^ m • (z s - cobd V s ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x)) =
      ((l : ℕ) : Qbar l) ^ m • z s - cobd V s x := by
  rw [smul_sub, ← map_smul, smul_inv_smul₀ (pow_ne_zero _ natCast_ne_zero')]

variable (c : Coef l) (V : R2 Ω l) (m k : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (x : Fin 2 → Qbar l)

theorem lift_mem (hVO : ∀ s i j, mat V s i j ∈ c.O) (hz : ∀ s i, z s i ∈ c.O) (hx : ∀ i, x i ∈ c.O)
    (hxc : ∀ s, Cv (m + k) (((l : ℕ) : Qbar l) ^ m • z s) (cobd V s x)) (s : G ℚ Ω) (j : Fin 2) :
    lift V m k z x s j ∈ c.O := by
  have hL : ((l : ℕ) : Qbar l) ∈ c.O := by
    have : ((l : ℕ) : Qbar l) = algebraMap ℤ_[l] (Qbar l) (l : ℤ_[l]) := by simp
    rw [this]; exact c.O.algebraMap_mem _
  have hD : ‖(z s - cobd V s ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x)) j‖ ≤ ‖((l : ℕ) : Qbar l) ^ k‖ := by
    have e := congrFun (smul_diff V m z x s) j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
    apply (norm_mul_pow_le_iff m k _).1
    simp only [Pi.sub_apply]
    rw [e]
    have := hxc s j
    unfold Cg at this
    simpa using this
  have e2 := congrFun (smul_lift V m k z x s) j
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hn : ‖lift V m k z x s j‖ ≤ 1 := by
    have := (norm_mul_pow_le_iff k 0 (lift V m k z x s j)).1 (by rw [e2, add_zero]; exact hD)
    simpa using this
  refine mem_of_mul c (m + k) ?_ hn
  have e3 := congrFun (smul_diff V m z x s) j
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e3
  rw [pow_add, mul_assoc, e2]
  simp only [Pi.sub_apply] at e3 ⊢
  rw [mul_sub] at e3 ⊢
  rw [e3, cobd_apply]
  refine c.O.sub_mem (c.O.mul_mem (c.O.pow_mem hL _) (hz s j)) (c.O.sub_mem ?_ (hx j))
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hVO _ _ _) (hx _)) (c.O.mul_mem (hVO _ _ _) (hx _))

theorem lift_coc (hz : ∀ s t, Cv (m + k) (z (s * t)) (z s + mat V s *ᵥ z t)) (s t : G ℚ Ω) :
    Cv m (lift V m k z x (s * t)) (lift V m k z x s + mat V s *ᵥ lift V m k z x t) := by
  refine cv_of_smul (k := k) (w := z (s * t)) (w' := z s + mat V s *ᵥ z t) ?_ (by rw [add_comm]; exact hz s t)
  rw [smul_sub, smul_add, ← Matrix.mulVec_smul, smul_lift, smul_lift, smul_lift, cobd_mul, Matrix.mulVec_sub]
  abel

theorem lift_ker (a : G ℚ Ω) (ha : mat V a = 1) (hz : Cv (m + k) (z a) 0) : Cv m (lift V m k z x a) 0 := by
  refine cv_of_smul (k := k) (w := z a) (w' := 0) ?_ (by rw [add_comm]; exact hz)
  rw [sub_zero, sub_zero, smul_lift, cobd_apply, ha, Matrix.one_mulVec, sub_self, sub_zero]

theorem cob_of_lift (hVO : ∀ s i j, mat V s i j ∈ c.O) (z' : G ℚ Ω → Fin 2 → Qbar l) (x' : Fin 2 → Qbar l)
    (hx : ∀ i, x i ∈ c.O) (hx' : ∀ i, x' i ∈ c.O) (hd : ∀ j, ‖x j - x' j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖)
    (h : Cob1 c m V ⊤ (lift V m k z x - lift V m k z' x')) : Cob1 c (m + k) V ⊤ (z - z') := by
  obtain ⟨v, hvO, hv⟩ := h
  set d : Fin 2 → Qbar l := (((l : ℕ) : Qbar l) ^ m)⁻¹ • (x - x') with hd'
  have hL : ((l : ℕ) : Qbar l) ∈ c.O := by
    have : ((l : ℕ) : Qbar l) = algebraMap ℤ_[l] (Qbar l) (l : ℤ_[l]) := by simp
    rw [this]; exact c.O.algebraMap_mem _
  have hdO : ∀ j, d j ∈ c.O := by
    intro j
    have e : ((l : ℕ) : Qbar l) ^ m * d j = x j - x' j := by
      simp only [hd', Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ natCast_ne_zero'), one_mul]
    refine mem_of_mul c m (by rw [e]; exact c.O.sub_mem (hx j) (hx' j)) ?_
    have := (norm_mul_pow_le_iff m 0 (d j)).1 (by rw [e, add_zero]; exact hd j)
    simpa using this
  refine ⟨d + ((l : ℕ) : Qbar l) ^ k • v, fun j => c.O.add_mem (hdO j) ?_, fun s _ => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; exact c.O.mul_mem (c.O.pow_mem hL _) (hvO j)
  have hs := hv s (Subgroup.mem_top s)
  rw [add_comm m k]
  refine cv_smul (a := (lift V m k z x - lift V m k z' x') s) (b := mat V s *ᵥ v - v) ?_ hs
  have e1 : (((l : ℕ) : Qbar l) ^ m)⁻¹ • x = (((l : ℕ) : Qbar l) ^ m)⁻¹ • x' + d := by
    rw [hd', smul_sub]; abel
  have e2 := smul_lift V m k z x s
  have e3 := smul_lift V m k z' x' s
  rw [e1, map_add (f := _)] at e2
  simp only [Pi.sub_apply, smul_sub]
  rw [e2, e3, ← cobd_apply V s (d + _), map_add (f := _), cobd_apply V s (_ • v), Matrix.mulVec_smul]
  abel

end GlobalTheory.Ord2.TorsBound

namespace GlobalTheory.Ord2.TorsBound

open GlobalTheory.Ord2.GwCount

theorem tors_bound : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ n : ℕ, ∃ B : ℕ, ∀ (N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, Coc1 c n (dual1 W) ⊤ (z i) ∧ ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z i a) 0) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → N ≤ B) → ∀ m : ℕ, ∃ B : ℕ, ∀ (n N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → (∀ i, Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z i s)) → N ≤ B := by
  intro l _ Ω _ _ _ e S A W hW c hWc hyp m
  choose Bf hBf using hyp
  have hVc : Continuous fun s => mat (dual1 W) s := continuous_mat_dual1 W hW.cont hW.det2
  have hVO : ∀ s i j, mat (dual1 W) s i j ∈ c.O := CupCob.dual_representation_integral c W hW.det2 hWc
  have hDI : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ (dual1 W).ker := by
    intro w hw B hB σ hσ
    have h1 : W σ = 1 := hW.unr w hw B hB hσ
    have hm : mat W σ = 1 := by simp [mat, h1]
    have he : eps l σ = 1 := eps_eq_one_of_mem_Ine (fun h => hw (hW.above w h)) hB hσ
    show dual1 W σ = 1
    apply Units.ext
    show mat (dual1 W) σ = 1
    rw [mat_dual1_eq' W hW.det2, hm, he, Matrix.det_one, mul_one, one_smul]
  have hVK : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, mat (dual1 W) a = 1 := by
    intro a ha
    have hker : (toGS Ω (S : Set Pl)).ker = NS Ω (S : Set Pl) := QuotientGroup.ker_mk' _
    rw [hker] at ha
    have hU : Unr (dual1 W) (0 : G ℚ Ω → Fin 2 → Qbar l) := fun w _ =>
      ⟨placeOf Ω w, isPlaceOver_placeOf Ω w, 0, fun s _ => by simp⟩
    exact (vanish_NS hW.above (dual1 W) hVc (Submodule.zero_mem _) hU hDI a ha).1
  obtain ⟨T, _, cls, hcls⟩ := exists_cls c m
  refine ⟨max ((Finset.range m).sup Bf) (Fintype.card T * Bf m), ?_⟩
  intro n N z hz hnc hcob
  by_cases hnm : n < m
  · exact (hBf n N z (fun i => ⟨(hz i).1, (hz i).2.1⟩) hnc).trans
      ((Finset.le_sup (f := Bf) (Finset.mem_range.2 hnm)).trans (le_max_left _ _))
  push_neg at hnm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  refine le_trans ?_ (le_max_right _ _)
  choose x hxO hx using hcob
  by_contra hlt
  push_neg at hlt
  let f : Fin N → T := fun i => cls (fun j => ⟨x i j, hxO i j⟩)
  classical
  obtain ⟨t, ht⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (by rw [Fintype.card_fin]; exact hlt)
  set F := Finset.univ.filter (fun i => f i = t) with hF
  let emb : Fin F.card → Fin N := fun k => (F.equivFin.symm k : Fin N)
  have hemb : ∀ a, f (emb a) = t := fun a => (Finset.mem_filter.1 (F.equivFin.symm a).2).2
  have hinj : Function.Injective emb := fun a b h => F.equivFin.symm.injective (Subtype.ext h)
  have hzc : ∀ i, Continuous (z i) := fun i => by
    have := (hz i).1.1
    rw [Subgroup.coe_top] at this
    exact continuousOn_univ.1 this
  have key := hBf m F.card (fun a => lift (dual1 W) m k (z (emb a)) (x (emb a))) ?_ ?_
  · omega
  · intro a
    refine ⟨⟨?_, fun s j => lift_mem c (dual1 W) m k _ _ hVO (hz (emb a)).1.2.1 (hxO (emb a))
      (fun s => hx (emb a) s (Subgroup.mem_top s)) s j,
      fun s _ t _ => lift_coc (dual1 W) m k _ _ (fun s t => (hz (emb a)).1.2.2 s (Subgroup.mem_top s) t
        (Subgroup.mem_top t)) s t⟩, fun b hb => lift_ker (dual1 W) m k _ _ b (hVK b hb) ((hz (emb a)).2.1 b hb)⟩
    apply Continuous.continuousOn
    show Continuous fun s => (((l : ℕ) : Qbar l) ^ k)⁻¹ • (z (emb a) s - (mat (dual1 W) s *ᵥ ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x (emb a)) - (((l : ℕ) : Qbar l) ^ m)⁻¹ • x (emb a)))
    exact ((hzc _).sub ((hVc.matrix_mulVec continuous_const).sub continuous_const)).const_smul ((((l : ℕ) : Qbar l) ^ k)⁻¹)
  · intro a b hab hcob
    refine hnc (emb a) (emb b) (fun h => hab (hinj h)) ?_
    refine cob_of_lift c (dual1 W) m k (z (emb a)) (x (emb a)) hVO (z (emb b)) (x (emb b)) (hxO _) (hxO _) ?_ hcob
    have := hcls _ _ ((hemb a).trans (hemb b).symm)
    simpa using this

end GlobalTheory.Ord2.TorsBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryInertiaIndependentStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_inertia_independent : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (q : Pl) (B B' : ValuationSubring Ω), (∀ s i j, mat W s i j ∈ c.O) → Coc1 c n W ⊤ z → IsPlaceOver B q → IsPlaceOver B' q → Cob1 c n W (Ine (F := ℚ) B) z → Cob1 c n W (Ine (F := ℚ) B') z := by
  first | exact @GlobalTheory.Ord2.CobConj.cob_conj | exact GlobalTheory.Ord2.CobConj.cob_conj | (intros; apply GlobalTheory.Ord2.CobConj.cob_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocycleVanishesOnKerToGSOfInertiaCoboundaryStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_vanishes_on_ker_toGS_of_inertia_coboundary : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (Y : G ℚ Ω → Fin 2 → Qbar l), Nf e S A W → Y ∈ Z1 (Loc.colRep W) → (∀ q : Pl, q ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, Y s = mat W s *ᵥ x - x) → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Y a = 0 := by
  first | exact @GlobalTheory.Ord2.GwCount.cocycle_zero_on_ker_toGS | exact GlobalTheory.Ord2.GwCount.cocycle_zero_on_ker_toGS | (intros; apply GlobalTheory.Ord2.GwCount.cocycle_zero_on_ker_toGS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductDualTwistIsTwoCocycleUnramifiedStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProductDualTwist_isTwoCocycle_unramified : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (W : R2 Ω l) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → ContainsAbove S l → (∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) → a ∈ Z1 (Loc.colRep W) → b ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, a s i ∈ c.O) → (∀ s i, b s i ∈ c.O) → Unr W a → Unr (dual1 W) b → Coc2 c n S (cup W a b) := by
  first | exact @GlobalTheory.Ord2.cupProductDualTwist_isTwoCocycle_unramified_alt | exact GlobalTheory.Ord2.cupProductDualTwist_isTwoCocycle_unramified_alt | (intros; apply GlobalTheory.Ord2.cupProductDualTwist_isTwoCocycle_unramified_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicCharCongruentOneOnDecompositionGroupStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicChar_congruent_one_on_decompositionGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl) (B : ValuationSubring Ω), IsPlaceOver B w → l ^ n ∣ normV w - 1 → 1 ≤ n → ∀ σ ∈ Dec (F := ℚ) B, Cg n (eps l σ) 1 := by
  first | exact @GlobalTheory.Ord2.EpsDec.eps_dec_cong | exact GlobalTheory.Ord2.EpsDec.eps_dec_cong | (intros; apply GlobalTheory.Ord2.EpsDec.eps_dec_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivCoboundaryOfReducedCocyclesCohomologous
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

theorem divCob_of_resCoc_cohom : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (z z' : G ℚ Ω → Fin 2 → Qbar l) (y y' : Fin 2 → Qbar l),
    VecE c y → VecE c y' → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) →
    (∀ s i, (l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i ∈ c.O) →
    (∃ m : ResPlane c, ∀ s, resCoc c W z y s - resCoc c W z' y' s = resAct c W hO s m - m) →
    z - z' ∈ divCob c W := by
  intro l _ Ω _ _ W c hO z z' y y' hy hy' hz hz' ⟨m, hm⟩

  have hlift : ∀ i, ∃ x : Qbar l, ∃ hx : x ∈ c.O, redL c x = m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (m i : ResL c)
    exact ⟨a.1, a.2, by rw [redL_of_mem c a.2]; exact ha⟩
  choose u hu hum using hlift
  have hl0 : (l : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hWu : ∀ s i, (mat W s *ᵥ u) i ∈ c.O := by
    intro s i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.add_mem (c.O.mul_mem (hO _ _ _) (hu 0)) (c.O.mul_mem (hO _ _ _) (hu 1))
  have hWuR : ∀ s i, redL c ((mat W s *ᵥ u) i) = (resAct c W hO s m) i := by
    intro s i
    rw [resAct_apply]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, wRed]
    rw [redL_add c (c.O.mul_mem (hO _ _ _) (hu 0)) (c.O.mul_mem (hO _ _ _) (hu 1)),
      redL_mul c (hO _ _ _) (hu 0), redL_mul c (hO _ _ _) (hu 1), hum 0, hum 1]
  have key : ∀ s i, ∃ o ∈ c.O, ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
      ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) - ((mat W s *ᵥ u) i - u i) = (l : Qbar l) * o := by
    intro s i
    have h1 := hz s i
    have h2 := hz' s i
    have h3 : (mat W s *ᵥ u) i - u i ∈ c.O := c.O.sub_mem (hWu s i) (hu i)
    have hmem := c.O.sub_mem (c.O.sub_mem h1 h2) h3
    refine (redL_eq_zero_iff c hmem).1 ?_
    have e := congrFun (hm s) i
    rw [redL_sub c (c.O.sub_mem h1 h2) h3, redL_sub c h1 h2, redL_sub c (hWu s i) (hu i), hWuR, hum]
    have e' : redL c ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
        redL c ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) = (resAct c W hO s m) i - m i := e
    rw [e', sub_self]
  choose o ho hoe using key
  refine ⟨(l : Qbar l)⁻¹ • (y - y' + u), ?_, fun s i => ?_⟩
  · obtain ⟨k, hk⟩ := hy
    obtain ⟨k', hk'⟩ := hy'
    refine ⟨k + k' + 1, fun i => ?_⟩
    have e : (l : Qbar l) ^ (k + k' + 1) * ((l : Qbar l)⁻¹ • (y - y' + u)) i =
        (l : Qbar l) ^ k' * ((l : Qbar l) ^ k * y i) - (l : Qbar l) ^ k * ((l : Qbar l) ^ k' * y' i)
          + (l : Qbar l) ^ (k + k') * u i := by
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      rw [pow_succ]; field_simp; ring
    rw [e]
    exact c.O.add_mem (c.O.sub_mem (c.O.mul_mem (natPow_mem c _) (hk i)) (c.O.mul_mem (natPow_mem c _) (hk' i)))
      (c.O.mul_mem (natPow_mem c _) (hu i))
  · have e : (z - z') s i - (mat W s *ᵥ ((l : Qbar l)⁻¹ • (y - y' + u)) - (l : Qbar l)⁻¹ • (y - y' + u)) i = o s i := by
      have h := hoe s i
      have e2 : (z - z') s i - (mat W s *ᵥ ((l : Qbar l)⁻¹ • (y - y' + u)) - (l : Qbar l)⁻¹ • (y - y' + u)) i =
          (l : Qbar l)⁻¹ * (((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
            ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) - ((mat W s *ᵥ u) i - u i)) := by
        simp only [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_sub, Pi.sub_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        field_simp; ring
      rw [e2, h, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
    rw [e]; exact ho s i

end GlobalTheory.Ord2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalMulApply
section
open GlobalTheory.KZ Matrix

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.gal_mul_apply (X : Tower Ω ε) (s s' : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal (s * s') f = X.gal s (X.gal s' f) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  show (X.exp (X.gal (s * s') f)).coeff r = (X.exp (X.gal s (X.gal s' f))).coeff r
  rw [X.gal_exp, X.gal_exp, X.gal_exp]
  rfl

theorem Tower.galB_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s s' : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) :
    X.galB l (s * s') b = X.galB l s (X.galB l s' b) := by
  funext u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Tower.kmap_kmap]
  have hg : X.gal (s * s') = (X.gal s').trans (X.gal s) := by
    ext f; exact X.gal_mul_apply s s' f
  have hc : (cyclotomicCharacter Ω l (s * s').toRingEquiv : ℤ_[l]) =
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (cyclotomicCharacter Ω l s'.toRingEquiv : ℤ_[l]) := by
    have : (s * s').toRingEquiv = s.toRingEquiv * s'.toRingEquiv := rfl
    rw [this, map_mul, Units.val_mul]
  rw [hg, hc]
  congr 2
  funext i
  fin_cases i <;> simp [mul_comm, mul_left_comm]

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsExtra
section

end

