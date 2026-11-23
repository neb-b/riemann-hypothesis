module

public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.Bundle0004

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfHaar
section
noncomputable section

open Formalism.IndefR.Datum Matrix MeasureTheory Topology

namespace Formalism.IndefR.Tow.SobPf

variable {n : ℕ}

theorem mul_mem_KAt {G s a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KAt G s) (hb : b ∈ KAt G s) :
    a * b ∈ KAt G s := by
  have ha' : a ∈ Formalism.QuantumDeterminants.UH G ∧ a * s = s * a := ha
  have hb' : b ∈ Formalism.QuantumDeterminants.UH G ∧ b * s = s * b := hb
  have h1 : aᴴ * G * a = G := ha'.1
  have h2 : bᴴ * G * b = G := hb'.1
  show a * b ∈ Formalism.QuantumDeterminants.UH G ∧ a * b * s = s * (a * b)
  refine ⟨?_, ?_⟩
  · show (a * b)ᴴ * G * (a * b) = G
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * G * (a * b) = bᴴ * (aᴴ * G * a) * b := by simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, h2]
  · calc a * b * s = a * (b * s) := Matrix.mul_assoc _ _ _
      _ = a * (s * b) := by rw [hb'.2]
      _ = (a * s) * b := (Matrix.mul_assoc _ _ _).symm
      _ = (s * a) * b := by rw [ha'.2]
      _ = s * (a * b) := Matrix.mul_assoc _ _ _

theorem inv_mem_KAt {G s a : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (ha : a ∈ KAt G s) :
    a⁻¹ ∈ KAt G s := by

  have ha' : a ∈ Formalism.QuantumDeterminants.UH G ∧ a * s = s * a := ha
  have h1 : aᴴ * G * a = G := ha'.1
  have hleft : (G⁻¹ * aᴴ * G) * a = 1 := by
    calc (G⁻¹ * aᴴ * G) * a = G⁻¹ * (aᴴ * G * a) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.nonsing_inv_mul G hG]
  have hdet : IsUnit a.det := Matrix.isUnit_det_of_left_inverse hleft
  have hright : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hdet
  have hleft' : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hdet
  show a⁻¹ ∈ Formalism.QuantumDeterminants.UH G ∧ a⁻¹ * s = s * a⁻¹
  refine ⟨?_, ?_⟩
  · show (a⁻¹)ᴴ * G * a⁻¹ = G
    calc (a⁻¹)ᴴ * G * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * G * a) * a⁻¹ := by rw [h1]
      _ = (a * a⁻¹)ᴴ * G * (a * a⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hright]; simp
  · calc a⁻¹ * s = a⁻¹ * s * (a * a⁻¹) := by rw [hright, Matrix.mul_one]
      _ = a⁻¹ * (s * a) * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = a⁻¹ * (a * s) * a⁻¹ := by rw [ha'.2]
      _ = (a⁻¹ * a) * s * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = s * a⁻¹ := by rw [hleft', Matrix.one_mul]

def Kg {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s}
  mul_mem' {a b} ha hb := by
    show ((a * b : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
    rw [Units.val_mul]; exact mul_mem_KAt ha hb
  one_mem' := by
    show ((1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
    rw [Units.val_one]; exact one_mem_KAt G s
  inv_mem' {a} ha := by
    show ((a⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
    rw [Matrix.coe_units_inv]; exact inv_mem_KAt (det_G_unit hs) ha

theorem isCompact_Kg {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) :
    IsCompact ((Kg hs : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ) : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) := by

  have hGu : IsUnit G.det := det_G_unit hs
  haveI : CompactSpace (KAt G s) := isCompact_iff_compactSpace.mp (isCompact_KAt hs)
  have hl : ∀ k ∈ KAt G s, (G⁻¹ * kᴴ * G) * k = 1 := fun k hk => by
    have h1 : kᴴ * G * k = G := (show k ∈ Formalism.QuantumDeterminants.UH G ∧ k * s = s * k from hk).1
    calc (G⁻¹ * kᴴ * G) * k = G⁻¹ * (kᴴ * G * k) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.nonsing_inv_mul G hGu]
  have hr : ∀ k ∈ KAt G s, k * (G⁻¹ * kᴴ * G) = 1 := fun k hk => by
    rw [← Matrix.inv_eq_left_inv (hl k hk)]
    exact Matrix.mul_nonsing_inv k (Matrix.isUnit_det_of_left_inverse (hl k hk))
  let F : KAt G s → (Matrix (Fin n) (Fin n) ℂ)ˣ := fun k =>
    ⟨k.1, G⁻¹ * k.1ᴴ * G, hr k.1 k.2, hl k.1 k.2⟩
  have hF : Continuous F := by
    rw [Units.continuous_iff]
    refine ⟨continuous_subtype_val, ?_⟩
    exact (continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul
      continuous_const
  have he : ((Kg hs : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ) : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) =
      Set.range F := by
    ext u
    constructor
    · intro hu
      exact ⟨⟨u.1, hu⟩, Units.ext rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2
  rw [he]
  exact isCompact_range hF

private theorem exists_Kg_coe_eq_of_mem_KAt {G s k : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) (hk : k ∈ KAt G s) :
    ∃ u : Kg hs, ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k := by
  have hGu : IsUnit G.det := det_G_unit hs
  have h1 : kᴴ * G * k = G := (show k ∈ Formalism.QuantumDeterminants.UH G ∧ k * s = s * k from hk).1
  have hleft : (G⁻¹ * kᴴ * G) * k = 1 := by
    calc (G⁻¹ * kᴴ * G) * k = G⁻¹ * (kᴴ * G * k) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.nonsing_inv_mul G hGu]
  have hdet : IsUnit k.det := Matrix.isUnit_det_of_left_inverse hleft
  exact ⟨⟨⟨k, k⁻¹, Matrix.mul_nonsing_inv k hdet, Matrix.nonsing_inv_mul k hdet⟩, hk⟩, rfl⟩

theorem haarExists_holds : HaarExists := by
  intro n G s hs
  haveI : CompactSpace (Kg hs) := isCompact_iff_compactSpace.mp (isCompact_Kg hs)
  letI : MeasurableSpace (Kg hs) := borel (Kg hs)
  haveI : BorelSpace (Kg hs) := ⟨rfl⟩
  let ν : Measure (Kg hs) := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    have h := Measure.haarMeasure_self (G := Kg hs) (K₀ := ⊤)
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at h
  let φ : Kg hs → (Fin n → Fin n → ℂ) := fun u =>
    Matrix.of.symm ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  have hφ : Continuous φ := by
    show Continuous (fun u : Kg hs => ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
    exact Units.continuous_val.comp continuous_subtype_val
  have hφm : Measurable φ := hφ.measurable
  have hcl : IsClosed {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := isClosed_KAt G s
  refine ⟨ν.map φ, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    rw [Measure.map_apply hφm MeasurableSet.univ, Set.preimage_univ]
    exact measure_univ
  · rw [ae_map_iff hφm.aemeasurable hcl.measurableSet]
    exact ae_of_all _ fun u => by
      show ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
      exact u.2
  · intro k₀ hk₀
    obtain ⟨u₀, hu₀⟩ := exists_Kg_coe_eq_of_mem_KAt hs hk₀
    have hT : Continuous (fun k : Fin n → Fin n → ℂ => Matrix.of.symm (k₀ * Matrix.of k)) := by
      show Continuous (fun k : Matrix (Fin n) (Fin n) ℂ => k₀ * k)
      exact continuous_const.matrix_mul continuous_id
    have hL : Measurable (fun u : Kg hs => u₀ * u) := (continuous_const.mul continuous_id).measurable
    have hcomp : (fun k : Fin n → Fin n → ℂ => Matrix.of.symm (k₀ * Matrix.of k)) ∘ φ =
        φ ∘ (fun u : Kg hs => u₀ * u) := by
      funext u
      show Matrix.of.symm (k₀ * ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
        Matrix.of.symm (((u₀ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
          ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
      rw [hu₀]
    rw [Measure.map_map hT.measurable hφm, hcomp, ← Measure.map_map hφm hL,
      map_mul_left_eq_self]
  · rintro U hU ⟨k, hkU, hkK⟩
    obtain ⟨u, hu⟩ := exists_Kg_coe_eq_of_mem_KAt hs hkK
    rw [Measure.map_apply hφm hU.measurableSet]
    refine (hU.preimage hφ).measure_pos ν ⟨u, ?_⟩
    show Matrix.of.symm ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ U
    rw [hu]
    exact hkU

end Formalism.IndefR.Tow.SobPf

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.HasStrictFDerivAtOneProd
section
noncomputable section

open Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

namespace Chart

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

theorem oneProd_succ {d : ℕ} (Y : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) (t : Fin (d + 1) → ℝ) :
    oneProd Y t = NormedSpace.exp (t 0 • Y 0) * oneProd (fun i => Y i.succ) (fun i => t i.succ) := by
  unfold oneProd
  rw [List.ofFn_succ, List.prod_cons]

theorem oneProd_zero : ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), oneProd Y 0 = 1 := by
  intro d Y
  simp [oneProd, NormedSpace.exp_zero]

theorem oneProd_mem (G : Matrix (Fin n) (Fin n) ℂ) :
    ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, Y i ∈ lieG G) → ∀ t : Fin d → ℝ,
      oneProd Y t ∈ Formalism.QuantumDeterminants.UH G := by
  intro d
  induction d with
  | zero =>
    intro Y _ t
    have h1 : oneProd Y t = 1 := by simp [oneProd]
    rw [h1]
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * 1 = G
    simp
  | succ d ih =>
    intro Y hY t
    rw [oneProd_succ]
    exact mul_mem_UH₂ G _ (expS_mem_UH (hY 0) (t 0)) _ (ih _ (fun i => hY i.succ) _)

def lin {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) : (Fin d → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (Y i)

theorem lin_apply {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℝ) :
    lin Y t = ∑ i, t i • Y i := by
  unfold lin
  simp

theorem hasStrictFDerivAt_oneProd : ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ),
    HasStrictFDerivAt (oneProd Y) (lin Y) 0 := by
  intro d
  induction d with
  | zero =>
    intro Y
    have h1 : oneProd Y = fun _ => 1 := funext fun t => by simp [oneProd]
    have h2 : lin Y = 0 := ContinuousLinearMap.ext fun t => by simp [lin_apply]
    rw [h1, h2]
    exact hasStrictFDerivAt_const _ _
  | succ d ih =>
    intro Y
    have hsplit : oneProd Y = fun t : Fin (d + 1) → ℝ =>
        NormedSpace.exp (t 0 • Y 0) * oneProd (fun i => Y i.succ) (fun i => t i.succ) :=
      funext fun t => oneProd_succ Y t
    let L0 : (Fin (d + 1) → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      (ContinuousLinearMap.proj (0 : Fin (d + 1))).smulRight (Y 0)
    let T : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ
    have ha : HasStrictFDerivAt (fun t : Fin (d + 1) → ℝ => NormedSpace.exp (t 0 • Y 0)) L0 0 := by
      have hz : L0 0 = 0 := map_zero L0
      have he : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
          (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (L0 0) := by
        rw [hz]
        exact hasStrictFDerivAt_exp_zero
      exact (he.comp (0 : Fin (d + 1) → ℝ) L0.hasStrictFDerivAt).congr_fderiv
        (ContinuousLinearMap.ext fun t => rfl)
    have hb : HasStrictFDerivAt (fun t : Fin (d + 1) → ℝ => oneProd (fun i => Y i.succ) (fun i => t i.succ))
        ((lin fun i => Y i.succ).comp T) 0 := by
      have hz : T 0 = 0 := map_zero T
      have hi : HasStrictFDerivAt (oneProd fun i => Y i.succ) (lin fun i => Y i.succ) (T 0) := by
        rw [hz]
        exact ih _
      exact hi.comp (0 : Fin (d + 1) → ℝ) T.hasStrictFDerivAt
    have hb0 : oneProd (fun i => Y i.succ) (fun _ => (0 : ℝ)) = 1 := oneProd_zero _
    have hm := ha.mul' hb
    rw [hsplit]
    refine hm.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun t => ?_
    have e1 : NormedSpace.exp ((0 : Fin (d + 1) → ℝ) 0 • Y 0) = 1 := by simp
    have e2 : oneProd (fun i => Y i.succ) (fun i => (0 : Fin (d + 1) → ℝ) i.succ) = 1 := hb0
    show NormedSpace.exp ((0 : Fin (d + 1) → ℝ) 0 • Y 0) * (lin (fun i => Y i.succ) (T t)) +
      L0 t * oneProd (fun i => Y i.succ) (fun i => (0 : Fin (d + 1) → ℝ) i.succ) = lin Y t
    rw [e1, e2, one_mul, mul_one, lin_apply, lin_apply, Fin.sum_univ_succ]
    exact add_comm _ _

end Chart

end Formalism.IndefR.Tow.SobPf

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.PdsEqIteratedFDeriv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexOrder

namespace Formalism.IndefR.Tow.SobPf.Avg

section Pds

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pds_eq_iteratedFDeriv (L : List (Fin N)) {f : (Fin N → ℝ) → E} (hf : ContDiff ℝ ∞ f) (r : Fin N → ℝ) :
    OrbStPf.pds L f r = iteratedFDeriv ℝ L.length f r (fun i => Pi.single (L.get i) 1) := by
  induction L generalizing r with
  | nil => simp [OrbStPf.pds]
  | cons i L ih =>
    have h2 : OrbStPf.pds L f = fun r => iteratedFDeriv ℝ L.length f r (fun j => Pi.single (L.get j) 1) :=
      funext ih
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ L.length f) r :=
      (hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) r
    show fderiv ℝ (OrbStPf.pds L f) r (Pi.single i 1) =
      iteratedFDeriv ℝ (L.length + 1) f r (fun k => Pi.single ((i :: L).get k) 1)
    rw [iteratedFDeriv_succ_apply_left, h2, fderiv_continuousMultilinear_apply_const_apply hd]
    rfl

end Pds

section Avg

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def Kset (G s : Matrix (Fin n) (Fin n) ℂ) : Set (Fin n → Fin n → ℂ) := {k | Matrix.of k ∈ KAt G s}

theorem isCompact_Kset {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsCompact (Kset G s) := isCompact_KAt hs

theorem isClosed_Kset (G s : Matrix (Fin n) (Fin n) ℂ) : IsClosed (Kset G s) := isClosed_KAt G s

def avgTerm (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : (Fin n → Fin n → ℂ) → ℂ) (w : H) {d : ℕ}
    (Xs : Fin d → Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℝ) (k : Fin n → Fin n → ℂ) : H :=
  p k • π (oneProd Xs t * Matrix.of k) w

theorem append_mem_lieG {G : Matrix (Fin n) (Fin n) ℂ} {d d' : ℕ} {X : Fin d → Matrix (Fin n) (Fin n) ℂ}
    {Y : Fin d' → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, X i ∈ lieG G) (hY : ∀ i, Y i ∈ lieG G) :
    ∀ i, Fin.append X Y i ∈ lieG G := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa using hX i
  · simpa using hY i

variable {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {w : H}
  (p : (Fin n → Fin n → ℂ) → ℂ)

theorem avgTerm_eq (hG : IsUnit G.det) (hπ : IsGRep G π) (hw : SmoothVec (lieG G) π w) {d d' : ℕ}
    {Xs : Fin d → Matrix (Fin n) (Fin n) ℂ} (hXs : ∀ i, Xs i ∈ lieG G) {Yc : Fin d' → Matrix (Fin n) (Fin n) ℂ}
    (hYc : ∀ i, Yc i ∈ lieG G) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Formalism.QuantumDeterminants.UH G) (s' : Fin d' → ℝ)
    {k : Fin n → Fin n → ℂ} (hk : Matrix.of k = u * oneProd Yc s') (t : Fin d → ℝ) :
    avgTerm π p w Xs t k = (p k • (π u).restrictScalars ℝ)
      (π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (appL d d' t + Fin.append 0 s')) w) := by
  have hdu : IsUnit u.det := by
    have h : uᴴ * G * u = G := hu
    have h' := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul] at h'
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h'
    exact hG.ne_zero h'.symm
  have hT : appL d d' t + Fin.append 0 s' = Fin.append t s' := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [appL]
  have hA : ∀ i, u⁻¹ * Xs i * u ∈ lieG G := fun i => conj_mem_lieG hG hu (hXs i)
  have hX : oneProd (fun i => u⁻¹ * Xs i * u) t * oneProd Yc s' ∈ Formalism.QuantumDeterminants.UH G := by
    rw [← oneProd_append]
    exact (smooth_oneProd hπ hw _ (append_mem_lieG hA hYc) _).2
  simp only [avgTerm]
  rw [hk, hT, oneProd_append, ← mul_assoc, oneProd_mul hdu, mul_assoc, hπ.2.1 u hu _ hX]
  rfl

variable {p}

theorem contDiff_orbit (hw : SmoothVec (lieG G) π w) {N : ℕ} {Z : Fin N → Matrix (Fin n) (Fin n) ℂ}
    (hZ : ∀ i, Z i ∈ lieG G) : ContDiff ℝ ∞ fun r => π (oneProd Z r) w :=
  Formalism.IndefR.Tow.OrbStPf.contDiff_orb (ρ := π) (Lie := lieG G) Z hZ hw 0

theorem pIter_avgTerm (hG : IsUnit G.det) (hπ : IsGRep G π) (hw : SmoothVec (lieG G) π w) {d d' : ℕ}
    {Xs : Fin d → Matrix (Fin n) (Fin n) ℂ} (hXs : ∀ i, Xs i ∈ lieG G) {Yc : Fin d' → Matrix (Fin n) (Fin n) ℂ}
    (hYc : ∀ i, Yc i ∈ lieG G) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Formalism.QuantumDeterminants.UH G) (s' : Fin d' → ℝ)
    {k : Fin n → Fin n → ℂ} (hk : Matrix.of k = u * oneProd Yc s') (j : ℕ) (t : Fin d → ℝ) :
    pIter (avgTerm π p w Xs) j t k = (p k • (π u).restrictScalars ℝ).compContinuousMultilinearMap
      ((iteratedFDeriv ℝ j (fun r => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) r) w)
        (Fin.append t s')).compContinuousLinearMap (fun _ => appL d d')) := by
  have hA : ∀ i, u⁻¹ * Xs i * u ∈ lieG G := fun i => conj_mem_lieG hG hu (hXs i)
  have hF := contDiff_orbit hw (append_mem_lieG hA hYc)
  have hT : appL d d' t + Fin.append 0 s' = Fin.append t s' := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [appL]
  have hfun : (fun t => avgTerm π p w Xs t k) = (p k • (π u).restrictScalars ℝ) ∘
      ((fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) ∘ appL d d') := by
    funext t
    exact avgTerm_eq p hG hπ hw hXs hYc hu s' hk t
  have hG1 : ContDiff ℝ ∞
      (fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) :=
    hF.comp (contDiff_id.add contDiff_const)
  have e1 : iteratedFDeriv ℝ j ((p k • (π u).restrictScalars ℝ) ∘
      ((fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) ∘ appL d d')) t =
      (p k • (π u).restrictScalars ℝ).compContinuousMultilinearMap (iteratedFDeriv ℝ j
        ((fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) ∘ appL d d') t) :=
    (p k • (π u).restrictScalars ℝ).iteratedFDeriv_comp_left (hG1.comp (appL d d').contDiff).contDiffAt
      (by exact_mod_cast le_top)
  have e2 : iteratedFDeriv ℝ j
      ((fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) ∘ appL d d') t =
      (iteratedFDeriv ℝ j
        (fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) (appL d d' t)).compContinuousLinearMap
        (fun _ => appL d d') :=
    (appL d d').iteratedFDeriv_comp_right hG1 t (by exact_mod_cast le_top)
  have e3 : iteratedFDeriv ℝ j
      (fun y => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) (y + Fin.append 0 s')) w) (appL d d' t) =
      iteratedFDeriv ℝ j (fun r => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) r) w)
        (appL d d' t + Fin.append 0 s') :=
    iteratedFDeriv_comp_add_right (f := fun r => π (oneProd (Fin.append (fun i => u⁻¹ * Xs i * u) Yc) r) w)
      j (Fin.append 0 s') (appL d d' t)
  unfold pIter
  rw [hfun, e1, e2, e3, hT]

theorem contDiff_avgTerm (hG : IsUnit G.det) (hπ : IsGRep G π) (hw : SmoothVec (lieG G) π w) {d : ℕ}
    {Xs : Fin d → Matrix (Fin n) (Fin n) ℂ} (hXs : ∀ i, Xs i ∈ lieG G) {k : Fin n → Fin n → ℂ}
    (hk : Matrix.of k ∈ Formalism.QuantumDeterminants.UH G) : ContDiff ℝ ∞ fun t => avgTerm π p w Xs t k := by
  have hk' : Matrix.of k = Matrix.of k * oneProd (fun i : Fin 0 => (i.elim0 : Matrix (Fin n) (Fin n) ℂ)) 0 := by
    rw [oneProd_zero, mul_one]
  have hY0 : ∀ i : Fin 0, (fun i : Fin 0 => (i.elim0 : Matrix (Fin n) (Fin n) ℂ)) i ∈ lieG G :=
    fun i => i.elim0
  have hF := contDiff_orbit hw (append_mem_lieG (fun i => conj_mem_lieG hG hk (hXs i)) hY0)
  have hfun : (fun t => avgTerm π p w Xs t k) = fun t =>
      (p k • (π (Matrix.of k)).restrictScalars ℝ)
        (π (oneProd (Fin.append (fun i => (Matrix.of k)⁻¹ * Xs i * Matrix.of k)
          (fun i : Fin 0 => (i.elim0 : Matrix (Fin n) (Fin n) ℂ))) (appL d 0 t + Fin.append 0 0)) w) := by
    funext t
    exact avgTerm_eq p hG hπ hw hXs hY0 hk 0 hk' t
  rw [hfun]
  exact (ContinuousLinearMap.contDiff _).comp (hF.comp ((appL d 0).contDiff.add contDiff_const))

end Avg

end Formalism.IndefR.Tow.SobPf.Avg

end
end

