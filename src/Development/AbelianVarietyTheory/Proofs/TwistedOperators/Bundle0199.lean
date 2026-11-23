module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalKill
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairingTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.PairTensor

open GlobalTheory.InvPairingTensor (exists_real_parts inner_act_skew exists_frame)

variable {p q : ℕ} {T : GrpData p q} (R : DSRep T)

theorem eq_zero_of_ctr (U : Type) [AddCommGroup U] [Module ℂ U] (y : R.HK.V ⊗[ℂ] U)
    (hy : ∀ v, ctr R U v y = 0) : y = 0 := by
  let m : R.HK.V → R.HK.V →ₗ[ℂ] ℂ := fun v => innerₛₗ ℂ (R.ι v) ∘ₗ R.ι
  have sepm : ∀ b, (∀ v, m v b = 0) → b = 0 := fun b h => by
    apply R.ι_inj
    rw [map_zero]
    exact inner_self_eq_zero.1 (h b)
  have key : ∀ v (z : R.HK.V ⊗[ℂ] U),
      GlobalTheory.PairingTensor.contrR (m v) (TensorProduct.comm ℂ _ _ z) = ctr R U v z := by
    intro v z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [TensorProduct.comm_tmul, GlobalTheory.PairingTensor.contrR_tmul, ctr_tmul]; rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  apply (TensorProduct.comm ℂ _ _).injective
  rw [map_zero]
  exact GlobalTheory.PairingTensor.eq_zero_of_contrR m sepm _ fun v => by rw [key, hy]

theorem ext_ctr (U : Type) [AddCommGroup U] [Module ℂ U] (z w : R.HK.V ⊗[ℂ] U)
    (h : ∀ v, ctr R U v z = ctr R U v w) : z = w := by
  rw [← sub_eq_zero]
  exact eq_zero_of_ctr R U _ fun v => by rw [map_sub, h, sub_self]

theorem ctr_add (U : Type) [AddCommGroup U] [Module ℂ U] (v w : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U (v + w) z = ctr R U v z + ctr R U w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [ctr_tmul, map_add (f := _), inner_add_left, add_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel

theorem ctr_smul (U : Type) [AddCommGroup U] [Module ℂ U] (c : ℂ) (v : R.HK.V)
    (z : R.HK.V ⊗[ℂ] U) : ctr R U (c • v) z = (starRingEnd ℂ) c • ctr R U v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [ctr_tmul, map_smul, inner_smul_left, mul_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]

theorem ctr_act (U : Type) [AddCommGroup U] [Module ℂ U] {X : Mat p q} (hX : X ∈ upq p q)
    (v : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U v (TensorProduct.map (R.HK.act X) LinearMap.id z) = -ctr R U (R.HK.act X v) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.map_tmul, ctr_tmul, ctr_tmul,
      eq_neg_of_add_eq_zero_left (inner_act_skew R hX v a), neg_smul, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, neg_add]

variable {W U : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  (a : Mat p q →ₗ[ℂ] Module.End ℂ W)

theorem exists_finiteDimensional_kill (ha : IsGK a) (hA : AdmGK R.HK)
    (B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PInv a R B) (P : W) :
    ∃ E : Submodule ℂ R.HK.V, FiniteDimensional ℂ E ∧
      ∀ y, (∀ x ∈ E, inner ℂ (R.ι y) (R.ι x) = 0) → B P y = 0 := by
  obtain ⟨W₀, hW, hP, hst⟩ := ha.2.1 P
  obtain ⟨E, hE, hE'⟩ := _root_.GlobalTheory.KHomFinite.exists_finiteDimensional_forall_map_mem p q R.HK hA _ a
    (fun Y Z _ _ => ha.1 Y Z) W₀ hW hst (fun v _ => ha.2.2 v)
  refine ⟨E, hE, fun y hy => ?_⟩
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  obtain ⟨F, hF, hyF, hFst⟩ := R.HK.kfin y
  obtain ⟨n, e, heF, he⟩ := exists_frame R.ι R.ι_inj F
  let φ : W →ₗ[ℂ] R.HK.V := ∑ j, (l ∘ₗ B.flip (e j)).smulRight (e j)
  have hφ : ∀ w, φ w = ∑ j, l (B w (e j)) • e j := fun w => by
    simp [φ, LinearMap.sum_apply]
  have hφF : ∀ w, φ w ∈ F := fun w => by
    rw [hφ]; exact F.sum_mem fun j _ => F.smul_mem _ (heF j)
  have hR : ∀ w, ∀ x ∈ F, inner ℂ (R.ι x) (R.ι (φ w)) = l (B w x) := fun w x hx => by
    conv_rhs => rw [← he x hx]
    rw [hφ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, inner_sum, inner_smul_right, LinearMap.map_smulₛₗ,
      inner_conj_symm, smul_eq_mul, mul_comm]
  have hreal : ∀ X ∈ upq p q, IsKC X → ∀ w, φ (a X w) = R.HK.act X (φ w) := by
    intro X hX hK w
    have hd : φ (a X w) - R.HK.act X (φ w) ∈ F :=
      F.sub_mem (hφF _) (hFst X hK _ (hφF w))
    have h0 : ∀ x ∈ F, inner ℂ (R.ι x) (R.ι (φ (a X w) - R.HK.act X (φ w))) = 0 := by
      intro x hx
      have h1 := inner_act_skew R hX x (φ w)
      have h2 := congrArg l (hB X hX w x)
      rw [map_add (f := _), map_zero] at h2
      rw [hR w _ (hFst X hK x hx)] at h1
      rw [map_sub, inner_sub_right, hR _ x hx]
      linear_combination h2 - h1
    rw [← sub_eq_zero]
    apply R.ι_inj
    rw [map_zero]
    exact inner_self_eq_zero.1 (h0 _ hd)
  have heq : ∀ Z, IsKC Z → ∀ w, φ (a Z w) = R.HK.act Z (φ w) := by
    intro Z hZ w
    obtain ⟨X, Y, hX, hY, hK, rfl⟩ := exists_real_parts Z
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hreal X hX (hK hZ).1, hreal Y hY (hK hZ).2]
  rw [← hR P y hyF]
  exact hy _ (hE' φ heq P hP)

theorem exists_pairing (f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U)
    (hf : ∀ Z, f ∘ₗ a Z = TensorProduct.map (R.HK.act Z) LinearMap.id ∘ₗ f) :
    ∃ B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U, PInv a R B ∧ ∀ P v, B P v = ctr R U v (f P) := by
  let B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U :=
    { toFun := fun P =>
        { toFun := fun v => ctr R U v (f P)
          map_add' := fun v w => ctr_add R U v w _
          map_smul' := fun c v => ctr_smul R U c v _ }
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  refine ⟨B, fun Z hZ P v => ?_, fun _ _ => rfl⟩
  change ctr R U v (f (a Z P)) + ctr R U (R.HK.act Z v) (f P) = 0
  have := LinearMap.congr_fun (hf Z) P
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at this
  rw [this, ctr_act R U hZ, neg_add_cancel]

theorem exists_map (ha : IsGK a) (hA : AdmGK R.HK)
    (B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PInv a R B) :
    ∃ f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U,
      (∀ Z, f ∘ₗ a Z = TensorProduct.map (R.HK.act Z) LinearMap.id ∘ₗ f) ∧
        ∀ P v, B P v = ctr R U v (f P) := by
  have ex : ∀ P, ∃ z : R.HK.V ⊗[ℂ] U, ∀ y, ctr R U y z = B P y := by
    intro P
    obtain ⟨E, hE, hkill⟩ := exists_finiteDimensional_kill R a ha hA B hB P
    obtain ⟨n, e, heE, he⟩ := exists_frame R.ι R.ι_inj E
    refine ⟨∑ j, e j ⊗ₜ[ℂ] B P (e j), fun y => ?_⟩
    have h1 := hkill (y - ∑ j, inner ℂ (R.ι (e j)) (R.ι y) • e j) (fun x hx => by
      rw [map_sub, inner_sub_left, sub_eq_zero]
      conv_lhs => rw [← he x hx]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_right, inner_smul_left,
        inner_conj_symm, mul_comm])
    rw [map_sub, sub_eq_zero] at h1
    rw [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ctr_tmul, LinearMap.map_smulₛₗ, inner_conj_symm]
  choose g hg using ex
  let f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U :=
    { toFun := g
      map_add' := fun P Q => ext_ctr R U _ _ fun y => by
        rw [map_add (f := _), hg, hg, hg, map_add (f := _), LinearMap.add_apply]
      map_smul' := fun t P => ext_ctr R U _ _ fun y => by
        rw [map_smul, hg, hg, map_smul, RingHom.id_apply, LinearMap.smul_apply] }
  have hf : ∀ P y, ctr R U y (f P) = B P y := hg
  have hreal : ∀ X ∈ upq p q, ∀ P,
      f (a X P) = TensorProduct.map (R.HK.act X) LinearMap.id (f P) := by
    intro X hX P
    refine ext_ctr R U _ _ fun y => ?_
    rw [ctr_act R U hX, hf, hf]
    exact eq_neg_of_add_eq_zero_left (hB X hX P y)
  refine ⟨f, fun Z => ?_, fun P y => (hf P y).symm⟩
  obtain ⟨X, Y, hX, hY, -, rfl⟩ := exists_real_parts Z
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.comp_apply, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    TensorProduct.map_add_left, TensorProduct.map_smul_left, hreal X hX, hreal Y hY]

end GlobalTheory.ArchRec.PairTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalNormClassesEqLocalUnramifiedCM
section
open Set Filter Polynomial NumberField IsDedekindDomain
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.TrEll.Hasse

abbrev Ten {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r) (k : Type) [CommRing k]
    [Algebra F k] : Type := k ⊗[F] Fld P

section Bridge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  (P : PPol (IsCMField.complexConj E).toAlgHom r)

def toSR : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r :=
  ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.1, by rw [coeff_zero_eq_eval_zero]; exact P.2.2.2.2.1, by
    have h := P.2.2.2.2.2
    rw [sharp, ← coeff_zero_eq_eval_zero] at h
    exact h⟩

variable (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]

def incl : k ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.plus (toSR P) →+* Ten P k :=
  (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.inclPlus (toSR P) k).toRingHom

theorem incl_injective : Function.Injective (incl P k) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := k) (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.plus (toSR P)).val.toLinearMap
    Subtype.val_injective

theorem sigR_incl (a) : sigR k (star' P) (incl P k a) = incl P k a :=
  GlobalTheory.TraceClasses.involBase_inclPlus (toSR P) k a

theorem exists_incl_eq_add (z : Ten P k) : ∃ a, incl P k a = z + sigR k (star' P) z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s y =>
    refine ⟨s ⊗ₜ ⟨y + star' P y, ?_⟩, TensorProduct.tmul_add _ _ _⟩
    change star' P (y + star' P y) = y + star' P y
    have : star' P (star' P y) = y := GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_invol (toSR P) y
    rw [map_add (f := _), this, add_comm]
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]; ring⟩

theorem exists_incl_eq {z : Ten P k} (hz : sigR k (star' P) z = z) : ∃ a, incl P k a = z := by
  obtain ⟨a, ha⟩ := exists_incl_eq_add P k ((2⁻¹ : maximalRealSubfield E) • z)
  refine ⟨a, ?_⟩
  have : sigR k (star' P) ((2⁻¹ : maximalRealSubfield E) • z) = (2⁻¹ : maximalRealSubfield E) • sigR k (star' P) z :=
    map_smul (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k) (star' P)) _ _
  rw [ha, this, hz, ← add_smul]
  norm_num

def unitMap : (k ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.plus (toSR P))ˣ →* plusUnits P k :=
  (Units.map (incl P k).toMonoidHom).codRestrict _ fun a => Units.ext (sigR_incl P k a)

theorem unitMap_surjective : Function.Surjective (unitMap P k) := by
  intro x
  obtain ⟨a, ha⟩ := exists_incl_eq P k (z := x.1.1) (congrArg Units.val x.2)
  obtain ⟨b, hb⟩ := exists_incl_eq P k (z := (x⁻¹).1.1) (congrArg Units.val (x⁻¹).2)
  have h : a * b = 1 := incl_injective P k (by rw [map_mul, ha, hb, map_one]; exact x.1.mul_inv)
  exact ⟨Units.mkOfMulEqOne a b h, Subtype.ext (Units.ext ha)⟩

theorem mk_unitMap_eq_iff (a b) : (QuotientGroup.mk (unitMap P k a) : Cls P k) = QuotientGroup.mk (unitMap P k b) ↔
    (QuotientGroup.mk a : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.NormClass (toSR P) k) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul]
  rfl

def clsMap : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.NormClass (toSR P) k →* Cls P k :=
  QuotientGroup.map _ _ (unitMap P k) fun _ h => h

theorem clsMap_injective : Function.Injective (clsMap P k) := by
  intro q q' h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q'
  exact (mk_unitMap_eq_iff P k a b).1 h

theorem clsMap_surjective : Function.Surjective (clsMap P k) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, rfl⟩ := unitMap_surjective P k x
  exact ⟨QuotientGroup.mk a, rfl⟩

theorem hform_eq (J : Matrix (Fin r) (Fin r) E) (u u' : Fin r → k ⊗[maximalRealSubfield E] E) :
    Formalism.UG.hform (sigR k (IsCMField.complexConj E).toAlgHom) (JR k J) u' u = GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.gramForm k Jᵀ u u' := by
  rw [Formalism.UG.hform, GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.gramForm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change GlobalTheory.HermLocal.ccBase E k (u' j) * ((1 : k) ⊗ₜ[maximalRealSubfield E] J j i) * u i =
    u i * ((1 : k) ⊗ₜ[maximalRealSubfield E] J j i) * GlobalTheory.HermLocal.ccBase E k (u' j)
  ring

theorem isometric_iff (J : Matrix (Fin r) (Fin r) E) (a) :
    (∃ φ, IsIsom P k J (incl P k a) φ) ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Isometric (toSR P) k Jᵀ a := by
  constructor
  · rintro ⟨φ, h⟩
    exact ⟨φ.toAddEquiv, fun e y => φ.map_smul e y, fun y y' => (hform_eq k J _ _).symm.trans (h y y')⟩
  · rintro ⟨φ, h1, h2⟩
    exact ⟨{ φ with map_smul' := h1 }, fun y y' => (hform_eq k J _ _).trans (h2 y y')⟩

theorem clsMap_mem_iff (J : Matrix (Fin r) (Fin r) E) (q) :
    clsMap P k q ∈ XSet P k J ↔ q ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.classes (toSR P) k Jᵀ := by
  constructor
  · rintro ⟨x, φ, e, h⟩
    obtain ⟨a, rfl⟩ := unitMap_surjective P k x
    exact ⟨a, clsMap_injective P k e, (isometric_iff P k J a.1).1 ⟨φ, h⟩⟩
  · rintro ⟨a, rfl, h⟩
    obtain ⟨φ, h⟩ := (isometric_iff P k J a.1).2 h
    exact ⟨unitMap P k a, φ, rfl, h⟩

theorem incl_toLocalPlus (a) : incl P k (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.toLocalPlus (toSR P) k a) =
    Algebra.TensorProduct.map (Algebra.ofId (maximalRealSubfield E) k) (AlgHom.id _ (Fld P))
      (incl P (maximalRealSubfield E) a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; exact (map_zero _).symm
  | tmul a b => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]; exact (map_add _ _ _).symm

theorem mapsCls_iff (q) (c : Cls P k) :
    MapsCls P (k := maximalRealSubfield E) (Algebra.ofId (maximalRealSubfield E) k) (clsMap P _ q) c ↔
      c = clsMap P k (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.toLocal (toSR P) k q) := by
  constructor
  · rintro ⟨x, x', e, rfl, h⟩
    obtain ⟨a, rfl⟩ := unitMap_surjective P _ x
    obtain rfl : QuotientGroup.mk a = q := clsMap_injective P _ e
    refine congrArg QuotientGroup.mk (Subtype.ext (Units.ext ?_))
    exact h.trans (incl_toLocalPlus P k a.1).symm
  · rintro rfl
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨unitMap P _ a, unitMap P k (Units.map (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.toLocalPlus (toSR P) k).toMonoidHom a), rfl, rfl,
      incl_toLocalPlus P k a.1⟩

end Bridge

theorem rational_eq_local : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → (∀ q q' : Cls P F, q ∈ XSet P F J → q' ∈ XSet P F J → (∀ v : HeightOneSpectrum (𝓞 F), ∃ a : Cls P (Fv F v), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q a ∧ MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q' a) → (∀ w : InfinitePlace F, ∃ a : Cls P w.Completion, MapsCls P (k := F) (Algebra.ofId F w.Completion) q a ∧ MapsCls P (k := F) (Algebra.ofId F w.Completion) q' a) → q = q') ∧ ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion), (∀ v, qf v ∈ XSet P (Fv F v) J) → (∀ w, qa w ∈ XSet P w.Completion J) → (∀ᶠ v in cofinite, qf v = 1) → ∃ q : Cls P F, q ∈ XSet P F J ∧ (∀ v : HeightOneSpectrum (𝓞 F), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q (qf v)) ∧ ∀ w : InfinitePlace F, MapsCls P (k := F) (Algebra.ofId F w.Completion) q (qa w) := by
  intro E _ _ F _ σ hcm hur r P J hJ
  obtain ⟨h1, h2, h3, h4⟩ := hcm
  haveI : Algebra.IsQuadraticExtension F E := ⟨h3⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  obtain rfl : F = maximalRealSubfield E := CMExtension.eq_maximalRealSubfield E F
  obtain rfl : σ = (IsCMField.complexConj E).toAlgHom := by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact AlgHom.ext fun x => φ.injective ((h4 φ x).trans (IsCMField.complexEmbedding_complexConj E φ x).symm)
  have H := GlobalTheory.TraceClasses.rationalEqAdelic E hur r Jᵀ (fun a b => hJ.1 a b)
    (by rw [Matrix.det_transpose]; exact hJ.2) (toSR P)
  constructor
  · intro q q' hq hq' hf ha
    obtain ⟨q, rfl⟩ := clsMap_surjective P _ q
    obtain ⟨q', rfl⟩ := clsMap_surjective P _ q'
    refine congrArg _ (H.injOn ((clsMap_mem_iff P _ J q).1 hq) ((clsMap_mem_iff P _ J q').1 hq')
      (Prod.ext (funext fun v => ?_) (funext fun w => ?_)))
    · obtain ⟨a, e, e'⟩ := hf v
      exact clsMap_injective P _ (((mapsCls_iff P _ q a).1 e).symm.trans ((mapsCls_iff P _ q' a).1 e'))
    · obtain ⟨a, e, e'⟩ := ha w
      exact clsMap_injective P _ (((mapsCls_iff P _ q a).1 e).symm.trans ((mapsCls_iff P _ q' a).1 e'))
  · intro qf qa hf ha h1
    choose xf hxf using fun v => clsMap_surjective P _ (qf v)
    choose xa hxa using fun w => clsMap_surjective P _ (qa w)
    obtain ⟨q, hq, e⟩ := H.surjOn (show (xf, xa) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.adelicClasses (toSR P) Jᵀ from
      ⟨fun v => (clsMap_mem_iff P _ J _).1 (by rw [hxf]; exact hf v),
        fun w => (clsMap_mem_iff P _ J _).1 (by rw [hxa]; exact ha w), by
        refine (Filter.eventually_cofinite.1 h1).subset fun v hv hv1 => hv ?_
        have : xf v = 1 := clsMap_injective P _ (by rw [hxf, hv1, map_one])
        exact ⟨1, RingHom.isIntegralElem_one _, RingHom.isIntegralElem_one _, this.symm⟩⟩)
    refine ⟨clsMap P _ q, (clsMap_mem_iff P _ J q).2 hq, fun v => (mapsCls_iff P _ q _).2 ?_,
      fun w => (mapsCls_iff P _ q _).2 ?_⟩
    · exact (hxf v).symm.trans (congrArg _ (congrFun (congrArg Prod.fst e) v).symm)
    · exact (hxa w).symm.trans (congrArg _ (congrFun (congrArg Prod.snd e) w).symm)

end GlobalTheory.TrEll.Hasse
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemilinearInjectiveOfIndep
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

theorem semilinear_injective_of_indep {K L V W ι : Type} [Field K] [Field L] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module L W] {φ : K →+* L} (b : Module.Basis ι K V) (c : V →ₛₗ[φ] W)
    (h : LinearIndependent L fun a => c (b a)) : Function.Injective c := by
  refine (injective_iff_map_eq_zero c).2 fun v hv => ?_
  have hexp : c v = ∑ i ∈ (b.repr v).support, φ (b.repr v i) • c (b i) := by
    conv_lhs => rw [← b.linearCombination_repr v]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smulₛₗ c _ _
  have hz := linearIndependent_iff'.1 h (b.repr v).support (fun i => φ (b.repr v i)) (by rw [← hv, hexp])
  have hrepr : b.repr v = 0 := by
    ext i
    rw [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hne
    exact hne (φ.injective ((hz i (Finsupp.mem_support_iff.2 hne)).trans (map_zero φ).symm))
  exact b.repr.injective (hrepr.trans (map_zero _).symm)

theorem hkF_single_one {D : D7} (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (d : List ℤ)
    (F : Bridge.Gf V → W) (h : Bridge.Gf V) :
    GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F h = ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (h * (finHom V).rangeRestrict γ) := by
  simp only [GlobalTheory.Hk3.hkF]
  rw [Finsupp.sum_single_index, one_smul]
  exact zero_smul ℂ _

theorem hkF_transfer {D : D7} (V : HSp D) {K U W W' : Type} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] {φ σ : K →+* ℂ} (c₀ : U →ₛₗ[φ] W) (c₁ : U →ₛₗ[σ] W') (inj : Function.Injective c₀)
    (F : Bridge.Gf V → W) (F' : Bridge.Gf V → W') (hb : ∀ h, ∃ v, F h = c₀ v ∧ F' h = c₁ v)
    (P : Pl D.host.E) (d : List ℤ) (a : K) (e : GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F = φ a • F) :
    GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F' = σ a • F' := by
  choose v hv using hb
  funext h
  have e' := congrFun e h
  rw [hkF_single_one, Pi.smul_apply] at e'
  rw [hkF_single_one, Pi.smul_apply]
  have key : ∑ γ ∈ GlobalTheory.Hk3.rep V P d, v (h * (finHom V).rangeRestrict γ) = a • v h := by
    apply inj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smulₛₗ]
    simp only [← fun x => (hv x).1]
    exact e'
  simp only [fun x => (hv x).2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_smulₛₗ, ← key, map_sum]

theorem eigF_conj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_jV → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ a x, GlobalTheory.ConjScalar.EigK R i a x → GlobalTheory.ConjScalar.EigF R i (fun P d => σ (a P d)) (H.e (j x)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ gramR c0R c0L hT i σ c c₁ H j hc a x hx
  have hind : LinearIndependent ℂ fun k => c0L i (bVV D.what₂.LL (lamV D i) k) :=
    (Formalism.IndefR.Bridge.FamTie.mapL hT i).2.1
  have inj : Function.Injective (c0L i) := semilinear_injective_of_indep (bVV D.what₂.LL (lamV D i)) (c0L i) hind
  intro P d hG hL
  have e := hx P d hG hL
  exact hkF_transfer (Vc D i) (c0L i) c₁ inj _ _ (hc.base x) P d (a P d) e

end GlobalTheory.ConjScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemHermitianLatticeAdelicCompletionOfSmulLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevkSmul

theorem smul_mem_hatV : ∀ (D : D7) {k : ℕ} (L L' : Lt D.host.E k) (c : D.host.E), (∀ x ∈ L, c • x ∈ L') → ∀ u ∈ hatV L, ((1 : Af D.host.F) ⊗ₜ[D.host.F] c) • u ∈ hatV L' := by
  intro D k L L' c hc u hu
  unfold hatV Formalism.MainNotions.StandardLattice.latHat at hu ⊢
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨a, ha, c • x, hc x hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

end GlobalTheory.LevkSmul
end

