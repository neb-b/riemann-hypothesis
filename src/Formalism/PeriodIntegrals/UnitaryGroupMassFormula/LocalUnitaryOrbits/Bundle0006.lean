module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CrossMSmulRight

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CfCoe
section
noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem memA {a : ℕ} (X : lamA v Λ a) (i : Fin a) : (X : TupV (E := E) v n a) i ∈ latLoc (E := E) v Λ :=
  X.2 i

def cf (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) {a : ℕ}
    (X : lamA v Λ a) (i : Fin a) (p : Fin n) : OR (E := E) v :=
  ⟨hR (Fv F v) σ J (e p) ((X : TupV (E := E) v n a) i), (hSD _).1 (memA v Λ X i) _ (bas_mem v Λ he p)⟩

theorem cf_coe (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) {a : ℕ}
    (X : lamA v Λ a) (i : Fin a) (p : Fin n) :
    (cf σ J v Λ hSD he X i p : Fv F v ⊗[F] E) = hR (Fv F v) σ J (e p) ((X : TupV (E := E) v n a) i) := rfl

def phi (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) {K : Type} [CommRing K]
    (π : OR (E := E) v →+* K) (a : ℕ) : lamA v Λ a →+ (Fin a → Fin n → K) where
  toFun X := fun i p => π (cf σ J v Λ hSD he X i p)
  map_zero' := by
    funext i p
    have h : cf σ J v Λ hSD he (0 : lamA v Λ a) i p = 0 := by
      apply Subtype.ext
      rw [cf_coe]
      simp [hR, Formalism.UG.hform]
    simp only [h, map_zero, Pi.zero_apply]
  map_add' X Y := by
    funext i p
    have h : cf σ J v Λ hSD he (X + Y) i p = cf σ J v Λ hSD he X i p + cf σ J v Λ hSD he Y i p := by
      apply Subtype.ext
      simp only [cf_coe, AddSubgroup.coe_add, Pi.add_apply, Subring.coe_add]
      exact hR_add_right σ J v _ _ _
    simp only [h, map_add (f := _), Pi.add_apply]

theorem phi_apply (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) {K : Type}
    [CommRing K] (π : OR (E := E) v →+* K) {a : ℕ} (X : lamA v Λ a) (i : Fin a) (p : Fin n) :
    phi σ J v Λ hSD he π a X i p = π (cf σ J v Λ hSD he X i p) := rfl

end PI.OmLocU.Red
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfBas
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def unifO (ϖ : Fv F v) : AddSubgroup (v.adicCompletionIntegers F) where
  carrier := {x | ∃ d : v.adicCompletionIntegers F, (x : Fv F v) = ϖ * d}
  add_mem' := fun {x y} ⟨d, hd⟩ ⟨e, he⟩ => ⟨d + e, by
    rw [AddMemClass.coe_add, AddMemClass.coe_add, hd, he, mul_add]⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := fun {x} ⟨d, hd⟩ => ⟨-d, by
    rw [NegMemClass.coe_neg, NegMemClass.coe_neg, hd, mul_neg]⟩

def ResIdx : Prop :=
  ∀ ϖ : Fv F v, IsUnif v ϖ → (unifO v ϖ).index = Ideal.absNorm v.asIdeal

def LatBasO (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∃ b : Fin (2 * n) → (Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
    ∀ x, x ∈ latLoc (E := E) v Λ ↔ ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i

theorem sc_smul_smul (ϖ r : Fv F v) (y : Fin n → Fv F v ⊗[F] E) :
    sc (E := E) v ϖ • (r • y) = (ϖ * r) • y := by
  funext p
  show sc (E := E) v ϖ * (r • y p) = (ϖ * r) • y p
  rw [mul_smul, Algebra.smul_def ϖ, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem idxV_of (a : ℕ) (Y : TupV (E := E) v n a) (hB : LatBasO σ J ψ v Λ a Y) (hR : ResIdx v) :
    IdxV σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  obtain ⟨b, hb, hmem⟩ := hB hG
  let φ : (Fin (2 * n) → v.adicCompletionIntegers F) →+ latA v Λ :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have key : ((lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · rintro ⟨z, hz, hze⟩ i _
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        have : (DistribSMul.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E := E) v ϖ))
            (∑ i, (d i : Fv F v) • b i) = ∑ i, (ϖ * d i) • b i := by
          show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = _
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => sc_smul_smul v ϖ _ _
        rw [← this, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (c i : Fv F v) • b i
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sc_smul_smul, hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [hR ϖ hϖ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GramInvOHolds
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

def oEvS : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)

theorem oEvS_fg : (oEvS (E := E) v).FG := by
  let g : 𝓞 E →+ (Fv F v ⊗[F] E) :=
    (inclR (F := F) (Fv F v)).toAddMonoidHom.comp (algebraMap (𝓞 E) E).toAddMonoidHom
  have hfg : (Submodule.map g.toIntLinearMap ⊤).FG := Submodule.FG.map _ Module.Finite.fg_top
  obtain ⟨t, ht⟩ := hfg
  have himg : (fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ =
      ↑(Submodule.map g.toIntLinearMap ⊤) := by
    ext y
    simp [g] <;> rfl
  refine ⟨t, ?_⟩
  unfold oEvS
  rw [himg, ← ht, Submodule.span_span_of_tower]

theorem oEv_one : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  unfold OEv
  exact Submodule.subset_span ⟨1, Set.mem_univ _, by simp⟩

theorem one_add_inv {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    ∃ m ∈ OEv (E := E) v, (1 + sc (E := E) v ϖ * x) * m = 1 := by
  have hϖi : ϖ ∈ v.adicCompletionIntegers F := by
    unfold IsUnif at hϖ
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hϖ, ← WithZero.coe_one,
      WithZero.coe_le_coe]
    show Multiplicative.ofAdd (-1 : ℤ) ≤ Multiplicative.ofAdd 0
    exact Multiplicative.ofAdd_le.mpr (by norm_num)
  have hsc : ∀ z : Fv F v ⊗[F] E,
      sc (E := E) v ϖ * z = (⟨ϖ, hϖi⟩ : v.adicCompletionIntegers F) • z := by
    intro z
    unfold sc
    rw [Algebra.smul_def]
    rfl
  have hcomm : ∀ (r : v.adicCompletionIntegers F) (a b : Fv F v ⊗[F] E), a * (r • b) = r • (a * b) :=
    fun r a b => mul_smul_comm r a b
  let y := 1 + sc (E := E) v ϖ * x
  let N' : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Submodule.span (v.adicCompletionIntegers F) ((fun m => y * m) '' (OEv (E := E) v))
  have hN'sub : ∀ z ∈ N', ∃ m ∈ OEv (E := E) v, z = y * m := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨m, hm, rfl⟩ := hz
      exact ⟨m, hm, rfl⟩
    | zero => exact ⟨0, oEv_zero v, (mul_zero y).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨m1, hm1, rfl⟩ := ha
      obtain ⟨m2, hm2, rfl⟩ := hb
      exact ⟨m1 + m2, oEv_add v hm1 hm2, (mul_add y m1 m2).symm⟩
    | smul r a _ ha =>
      obtain ⟨m, hm, rfl⟩ := ha
      refine ⟨r • m, ?_, (hcomm r y m).symm⟩
      unfold OEv at hm ⊢
      exact Submodule.smul_mem _ r hm
  have hle : oEvS (E := E) v ≤ N' := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (oEvS_fg v)
      (IsLocalRing.maximalIdeal_le_jacobson _)
    intro m hm
    have hm' : m ∈ OEv (E := E) v := hm
    have hxm : x * m ∈ oEvS (E := E) v := oEv_mul v hx hm'
    have h1 : y * m ∈ N' := Submodule.subset_span ⟨m, hm', rfl⟩
    have h2 : (-(⟨ϖ, hϖi⟩ : v.adicCompletionIntegers F)) • (x * m) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • oEvS (E := E) v := by
      apply Submodule.smul_mem_smul _ hxm
      apply neg_mem
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      have hmul := congrArg (fun z : v.adicCompletionIntegers F => Valued.v (z : Fv F v)) u.mul_inv
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one, map_mul, map_one] at hmul
      have hui : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v) ≤ 1 :=
        (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (u⁻¹ : (v.adicCompletionIntegers F)ˣ).1.2
      rw [hu] at hmul
      unfold IsUnif at hϖ
      change Valued.v ϖ * _ = 1 at hmul
      rw [hϖ] at hmul
      have hlt : (↑(Multiplicative.ofAdd (-1 : ℤ)) : WithZero (Multiplicative ℤ)) < 1 := by
        rw [← WithZero.coe_one, WithZero.coe_lt_coe]
        show Multiplicative.ofAdd (-1 : ℤ) < Multiplicative.ofAdd 0
        exact Multiplicative.ofAdd_lt.mpr (by norm_num)
      have hcon : (1 : WithZero (Multiplicative ℤ)) ≤ ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
        calc (1 : WithZero (Multiplicative ℤ)) = _ := hmul.symm
          _ ≤ ↑(Multiplicative.ofAdd (-1 : ℤ)) * 1 := by gcongr
          _ = _ := mul_one _
      exact absurd hcon (not_le.mpr hlt)
    have hdecomp : m = y * m + (-(⟨ϖ, hϖi⟩ : v.adicCompletionIntegers F)) • (x * m) := by
      rw [neg_smul, ← hsc]
      simp only [y]
      ring
    rw [hdecomp]
    exact Submodule.add_mem_sup h1 h2
  have h1 : (1 : Fv F v ⊗[F] E) ∈ N' := hle (oEv_one v)
  obtain ⟨m, hm, hm1⟩ := hN'sub 1 h1
  exact ⟨m, hm, hm1.symm⟩

section Main

variable (Λ : Set (Fin n → E)) (ψ : AddChar (AF F) ℂ)

def oEvR : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := oEv_mul v
  one_mem' := oEv_one v
  add_mem' := oEv_add v
  zero_mem' := oEv_zero v
  neg_mem' := oEv_neg v

theorem det_sub_mem {a : ℕ} {ϖ : Fv F v} (hint : ϖ ∈ v.adicCompletionIntegers F)
    (A B : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ OEv (E := E) v)
    (hB : ∀ i j, B i j ∈ OEv (E := E) v) (hAB : ∀ i j, A i j - B i j ∈ PO (E := E) v ϖ) :
    A.det - B.det ∈ PO (E := E) v ϖ := by
  have hsc : sc (E := E) v ϖ ∈ OEv (E := E) v := by
    have h1 := oEv_one (E := E) v
    unfold OEv at h1 ⊢
    have h2 := Submodule.smul_mem _ (⟨ϖ, hint⟩ : v.adicCompletionIntegers F) h1
    convert h2 using 1
    simp [sc, Algebra.smul_def, Algebra.TensorProduct.one_def]
  let A' : Matrix (Fin a) (Fin a) (oEvR (E := E) v) := fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix (Fin a) (Fin a) (oEvR (E := E) v) := fun i j => ⟨B i j, hB i j⟩
  let s : oEvR (E := E) v := ⟨sc (E := E) v ϖ, hsc⟩
  have hdA : ((A'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) = A.det := by
    calc ((A'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) = (oEvR (E := E) v).subtype A'.det := rfl
      _ = ((oEvR (E := E) v).subtype.mapMatrix A').det := RingHom.map_det _ _
      _ = A.det := rfl
  have hdB : ((B'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) = B.det := by
    calc ((B'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) = (oEvR (E := E) v).subtype B'.det := rfl
      _ = ((oEvR (E := E) v).subtype.mapMatrix B').det := RingHom.map_det _ _
      _ = B.det := rfl
  have hmem : A'.det - B'.det ∈ Ideal.span {s} := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    obtain ⟨c, hc, hceq⟩ := hAB i j
    refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
    show c * sc (E := E) v ϖ = A i j - B i j
    rw [hceq, mul_comm]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  show ∃ c ∈ OEv (E := E) v, A.det - B.det = sc (E := E) v ϖ * c
  refine ⟨b, b.2, ?_⟩
  rw [← hdA, ← hdB]
  calc ((A'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) - B'.det
      = ((A'.det - B'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) := rfl
    _ = ((b * s : oEvR (E := E) v) : Fv F v ⊗[F] E) := by rw [hb]
    _ = sc (E := E) v ϖ * b := by
      show (b : Fv F v ⊗[F] E) * sc (E := E) v ϖ = _
      exact mul_comm _ _

theorem gramInvO_holds (a : ℕ) (Y : TupV (E := E) v n a) : GramInvO σ J v Λ ψ a Y := by
  intro hG ϖ hϖ y hy hd
  unfold GoodY at hG
  have hSD := hG.2.2.1
  have hy' : ∀ i, y i ∈ latLoc (E := E) v Λ := hy
  have hϖi : ϖ ∈ v.adicCompletionIntegers F := by
    unfold IsUnif at hϖ
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hϖ, ← WithZero.coe_one,
      WithZero.coe_le_coe]
    show Multiplicative.ofAdd (-1 : ℤ) ≤ Multiplicative.ofAdd 0
    exact Multiplicative.ofAdd_le.mpr (by norm_num)
  have hsc : sc (E := E) v ϖ ∈ OEv (E := E) v := by
    have h1 := oEv_one (E := E) v
    unfold OEv at h1 ⊢
    have h2 := Submodule.smul_mem _ (⟨ϖ, hϖi⟩ : v.adicCompletionIntegers F) h1
    convert h2 using 1
    simp [sc, Algebra.smul_def, Algebra.TensorProduct.one_def]
  have hyI : ∀ i j, gramR (Fv F v) σ J y i j ∈ OEv (E := E) v := fun i j =>
    hR_mem_oEv (σ := σ) (J := J) (v := v) (Λ := Λ) hSD (hy' i) (hy' j)
  have hYI : ∀ i j, gramR (Fv F v) σ J Y i j ∈ OEv (E := E) v := by
    intro i j
    obtain ⟨c, hc, hceq⟩ := hd i j
    have e : gramR (Fv F v) σ J Y i j = gramR (Fv F v) σ J y i j + -(sc (E := E) v ϖ * c) := by
      rw [← hceq]
      ring
    rw [e]
    exact oEv_add v (hyI i j) (oEv_neg v (oEv_mul v hsc hc))
  obtain ⟨w, hw, -, hdw⟩ := hG.2.2.2.2.2.2
  obtain ⟨c, hc, hceq⟩ := det_sub_mem v hϖi (gramR (Fv F v) σ J y) (gramR (Fv F v) σ J Y) hyI hYI hd
  have hwc : w * c ∈ OEv (E := E) v := oEv_mul v hw hc
  obtain ⟨m, hm, hm1⟩ := one_add_inv v hϖ hwc
  have e1 : (gramR (Fv F v) σ J y).det =
      (gramR (Fv F v) σ J Y).det + sc (E := E) v ϖ * c := by
    rw [← hceq]
    ring
  have e2 : (gramR (Fv F v) σ J y).det =
      (gramR (Fv F v) σ J Y).det * (1 + sc (E := E) v ϖ * (w * c)) := by
    linear_combination e1 - (sc (E := E) v ϖ * c) * hdw
  have hdy1 : (m * w) * (gramR (Fv F v) σ J y).det = 1 := by
    calc (m * w) * (gramR (Fv F v) σ J y).det
        = (gramR (Fv F v) σ J Y).det * w * ((1 + sc (E := E) v ϖ * (w * c)) * m) := by
          rw [e2]
          ring
      _ = 1 := by rw [hdw, hm1, one_mul]
  let A' : Matrix (Fin a) (Fin a) (oEvR (E := E) v) := fun i j => ⟨gramR (Fv F v) σ J y i j, hyI i j⟩
  have hadj : ∀ i j, (gramR (Fv F v) σ J y).adjugate i j ∈ OEv (E := E) v := by
    intro i j
    have e : (gramR (Fv F v) σ J y).adjugate = (oEvR (E := E) v).subtype.mapMatrix A'.adjugate := by
      rw [RingHom.map_adjugate]
      rfl
    rw [e]
    exact (A'.adjugate i j).2
  refine ⟨(m * w) • (gramR (Fv F v) σ J y).adjugate, fun i j => ?_, ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul]
    exact oEv_mul v (oEv_mul v hm hw) (hadj i j)
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hdy1, one_smul]

end Main

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmLocUOfOnto
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem omLocU_of_onto (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y) (hO : HensOnto σ J v Λ ψ a Y)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_hens σ J ψ v Λ a Y hSd hOm h1 hFull (fibHens_of σ J v Λ ψ a Y hO) h3 h4 h5

theorem omLocU_of_tr (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y) (hGI : GramInvO σ J v Λ ψ a Y) (hTr : TrOnto σ v)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_onto σ J ψ v Λ a Y hSd hOm h1 (hensOnto_of σ J v Λ ψ a Y hGI hTr) hFull h3 h4 h5

end PI.OmLocU
end
end

