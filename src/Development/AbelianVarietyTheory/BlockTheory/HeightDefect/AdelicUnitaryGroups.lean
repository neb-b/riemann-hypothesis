module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG

section Ring

variable {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem cT_map {m p : Type} (σ : A →+* A) (σ' : B →+* B) (φ : A → B) (h : ∀ x, σ' (φ x) = φ (σ x))
    (M : Matrix m p A) : cT σ' (M.map φ) = (cT σ M).map φ := by
  ext i j; simp [cT, h]

def mapU (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : ∀ x, σ' (φ x) = φ (σ x))
    (J : Matrix n n A) (J' : Matrix n n B) (hJ : J.map φ = J') : UJ σ J →* UJ σ' J' :=
  ((bc φ).comp (UJ σ J).subtype).codRestrict _ (by
    intro g
    have hg : cT σ ((g : GL n A) : Matrix n n A) * J * ((g : GL n A) : Matrix n n A) = J := g.2
    show cT σ' (((g : GL n A) : Matrix n n A).map φ) * J' * (((g : GL n A) : Matrix n n A).map φ) = J'
    rw [cT_map σ σ' φ h, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg])

def glue (j : B →ₙ+* A) (a : Matrix n n A) (b : Matrix n n B) : Matrix n n A :=
  (1 - j 1) • a + b.map j

theorem glue_mul (j : B →ₙ+* A) (a a' : Matrix n n A) (b b' : Matrix n n B) :
    glue j a b * glue j a' b' = glue j (a * a') (b * b') := by
  have h1 : ∀ y, j 1 * j y = j y := fun y => by rw [← map_mul, one_mul]
  ext r s
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [glue, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, map_sum, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination (a r k * a' k s) * h1 1 - a r k * h1 (b' k s) - a' k s * h1 (b r k)

theorem glue_one (j : B →ₙ+* A) : glue j (1 : Matrix n n A) 1 = 1 := by
  ext r s
  by_cases h : r = s
  · subst h; simp [glue]
  · simp [glue, h]

def extU (σ : B →+* B) (σ' : A →+* A) (j : B →ₙ+* A) (h : ∀ x, σ' (j x) = j (σ x))
    (J : Matrix n n B) (J' : Matrix n n A) (hJ : J.map j = j 1 • J') : UJ σ J →* UJ σ' J' :=
  ((Units.map (⟨⟨fun b => glue j 1 b, glue_one j⟩, fun b b' => by
      rw [glue_mul, one_mul]⟩ : Matrix n n B →* Matrix n n A)).comp (UJ σ J).subtype).codRestrict _ (by
    intro g
    have hg : cT σ ((g : GL n B) : Matrix n n B) * J * ((g : GL n B) : Matrix n n B) = J := g.2
    show cT σ' (glue j 1 ((g : GL n B) : Matrix n n B)) * J' * glue j 1 ((g : GL n B) : Matrix n n B) = J'
    have e1 : J' = glue j J' J := by rw [glue, hJ, ← add_smul]; simp
    have e2 : cT σ' (glue j 1 ((g : GL n B) : Matrix n n B)) =
        glue j 1 (cT σ ((g : GL n B) : Matrix n n B)) := by
      ext r s
      by_cases hrs : r = s
      · subst hrs; simp [glue, cT, h]
      · simp [glue, cT, h, hrs, Ne.symm hrs]
    rw [e2]
    conv_lhs => rw [e1]
    rw [glue_mul, glue_mul, hg, one_mul, mul_one, ← e1])

variable {m : Type} [Fintype m] [DecidableEq m]

theorem emb_mul (M : Matrix m n A) (P : Matrix n m A) (hP : P * M = 1) (a b : Matrix n n A) :
    (1 + M * (a - 1) * P) * (1 + M * (b - 1) * P) = 1 + M * (a * b - 1) * P := by
  have : M * (a - 1) * P * (M * (b - 1) * P) = M * ((a - 1) * (b - 1)) * P := by
    calc _ = M * (a - 1) * (P * M) * (b - 1) * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP]; simp only [Matrix.mul_assoc, Matrix.one_mul]
  have e : a * b - 1 = (b - 1) + (a - 1) + (a - 1) * (b - 1) := by noncomm_ring
  rw [e, add_mul, mul_add, mul_add, this]
  simp only [Matrix.mul_add, Matrix.add_mul, one_mul, mul_one, add_assoc]

def embU (σ : A →+* A) (GB : Matrix n n A) (GA : Matrix m m A) (M : Matrix m n A) (P : Matrix n m A)
    (hP : P * M = 1) (h1 : cT σ P * GB = GA * M) (h2 : cT σ M * GA = GB * P) :
    UJ σ GB →* UJ σ GA :=
  ((Units.map (⟨⟨fun a => 1 + M * (a - 1) * P, by simp⟩, fun a b =>
      (emb_mul M P hP a b).symm⟩ : Matrix n n A →* Matrix m m A)).comp
      (UJ σ GB).subtype).codRestrict _ (by
    intro g
    have hg : cT σ ((g : GL n A) : Matrix n n A) * GB * ((g : GL n A) : Matrix n n A) = GB := g.2
    show cT σ (1 + M * (((g : GL n A) : Matrix n n A) - 1) * P) * GA *
      (1 + M * (((g : GL n A) : Matrix n n A) - 1) * P) = GA
    generalize ((g : GL n A) : Matrix n n A) = x at hg
    have e : cT σ (1 + M * (x - 1) * P) = 1 + cT σ P * (cT σ x - 1) * cT σ M := by
      have a1 : ∀ y : Matrix m m A, cT σ (1 + y) = 1 + cT σ y := fun y => by
        rw [← cT_one σ]; ext r s; simp [cT, Matrix.one_apply, eq_comm]
      have a2 : cT σ (x - 1) = cT σ x - 1 := by
        conv_rhs => rw [← cT_one σ]
        ext r s; simp [cT, Matrix.one_apply, eq_comm]
      rw [a1, cT_mul, cT_mul, a2, Matrix.mul_assoc]
    have t1 : GA * (M * (x - 1) * P) = cT σ P * (GB * (x - 1)) * P := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← h1]; simp only [Matrix.mul_assoc]
    have t2 : cT σ P * (cT σ x - 1) * cT σ M * GA = cT σ P * ((cT σ x - 1) * GB) * P := by
      rw [Matrix.mul_assoc, h2]; simp only [Matrix.mul_assoc]
    have t3 : cT σ P * ((cT σ x - 1) * GB) * P * (M * (x - 1) * P) =
        cT σ P * ((cT σ x - 1) * GB * (x - 1)) * P := by
      calc _ = cT σ P * ((cT σ x - 1) * GB) * (P * M) * (x - 1) * P := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hP]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    have t4 : GB * (x - 1) + ((cT σ x - 1) * GB + (cT σ x - 1) * GB * (x - 1)) = 0 := by
      have : GB * (x - 1) + ((cT σ x - 1) * GB + (cT σ x - 1) * GB * (x - 1)) =
        cT σ x * GB * x - GB := by noncomm_ring
      rw [this, hg, sub_self]
    rw [e, add_mul, one_mul, t2, add_mul, mul_add, mul_add, mul_one, mul_one, t1, t3, add_assoc,
      ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add, t4]
    simp)

end Ring

section Points

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
variable {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

def mapH (φ : R →ₐ[F] R') : HA R σ J →* HA R' σ J :=
  mapU (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R' σ) (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
    (by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
      | add x y hx hy => simp only [map_add (f := _), hx, hy])
    (JR R J) (JR R' J) (by ext r s; simp [JR, inclR])

def diagH (R : Type) [CommRing R] [Algebra F R] : UJ (σ : E →+* E) J →* HA R σ J :=
  mapU (σ : E →+* E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (inclR R) (by intro x; simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR]) J (JR R J) rfl

def tensNU (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) : R ⊗[F] E →ₙ+* R' ⊗[F] E where
  toFun := TensorProduct.map j LinearMap.id
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [add_mul, map_add (f := _), hx, hx']
    | tmul a e =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [mul_add, map_add (f := _), hy, hy']
      | tmul b e' => simp [hj]

@[simp] theorem tensNU_tmul (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (a : R) (e : E) :
    tensNU j hj (a ⊗ₜ[F] e) = j a ⊗ₜ[F] e := rfl

def extH (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) : HA R σ J →* HA R' σ J :=
  extU (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R' σ) (tensNU j hj)
    (by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
      | add x y hx hy => simp only [map_add (f := _), hx, hy])
    (JR R J) (JR R' J) (by
      ext r s
      simp [JR, inclR, Algebra.TensorProduct.one_def])

end Points

section RealPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def placeOf (F : Type) [Field F] [Algebra F E] (τ : E →+* ℂ) : InfinitePlace F :=
  InfinitePlace.mk (τ.comp (algebraMap F E))

theorem placeOf_isReal (hc : CMData F E) (τ : E →+* ℂ) : (placeOf F τ).IsReal :=
  haveI := hc.totReal
  IsTotallyReal.isReal _

theorem ext_algebraMap (hc : CMData F E) (τ : E →+* ℂ) (a : F) :
    InfinitePlace.Completion.extensionEmbedding (placeOf F τ)
      (algebraMap F (placeOf F τ).Completion a) = τ (algebraMap F E a) := by
  have h1 : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) :=
    InfinitePlace.isReal_mk_iff.1 (placeOf_isReal hc τ)
  have h2 : (placeOf F τ).embedding = τ.comp (algebraMap F E) :=
    InfinitePlace.embedding_mk_eq_of_isReal h1
  have h3 := InfinitePlace.Completion.extensionEmbedding_coe (placeOf F τ)
    ((WithAbs.equiv (placeOf F τ).1).symm a)
  rw [RingEquiv.apply_symm_apply, h2] at h3
  simpa only [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply, RingHom.comp_apply, WithAbs.equiv_symm_apply] using h3

def locMap (hc : CMData F E) (τ : E →+* ℂ) : (placeOf F τ).Completion ⊗[F] E →+* ℂ :=
  letI : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  (Algebra.TensorProduct.productMap
    ({ InfinitePlace.Completion.extensionEmbedding (placeOf F τ) with
        commutes' := ext_algebraMap hc τ } : (placeOf F τ).Completion →ₐ[F] ℂ)
    ({ τ with commutes' := fun _ => rfl } : E →ₐ[F] ℂ)).toRingHom

end RealPlace

section Groups

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (V : HSpace E)

abbrev GA : Type := HA (AF F) hc.sig V.gram

abbrev GFin : Type := HA (Af F) hc.sig V.gram

abbrev GInf : Type := HA (Ainf F) hc.sig V.gram

abbrev GLoc (v : HeightOneSpectrum (𝓞 F)) : Type := HA (Fv F v) hc.sig V.gram

abbrev GRat : Type := UJ (hc.sig : E →+* E) V.gram

def projFin : GA hc V →* GFin hc V := mapH hc.sig V.gram (sndA F)

def projInf : GA hc V →* GInf hc V := mapH hc.sig V.gram (fstA F)

def projLoc (v : HeightOneSpectrum (𝓞 F)) : GFin hc V →* GLoc hc V v := mapH hc.sig V.gram (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)

def ofFin : GFin hc V →* GA hc V :=
  extH (R' := AF F) hc.sig V.gram (LinearMap.inr F (Ainf F) (Af F)) (fun a b => Prod.ext (mul_zero _).symm rfl)

def ofInf : GInf hc V →* GA hc V :=
  extH (R' := AF F) hc.sig V.gram (LinearMap.inl F (Ainf F) (Af F)) (fun a b => Prod.ext rfl (mul_zero _).symm)

def ratA : GRat hc V →* GA hc V := diagH hc.sig V.gram (AF F)

def ratPts : Subgroup (GA hc V) := (ratA hc V).range

def finPts : Subgroup (GA hc V) := (projInf hc V).ker

def realPts : Subgroup (GA hc V) := (projFin hc V).ker


def coordR (R : Type) [CommRing R] [Algebra F R] (x : V.V) : Fin V.rank → R ⊗[F] E :=
  fun i => inclR R (V.frame.repr x i)

def extSub (R : Type) [CommRing R] [Algebra F R] (W : Submodule E V.V) :
    Submodule (R ⊗[F] E) (Fin V.rank → R ⊗[F] E) :=
  Submodule.span _ (coordR (F := F) V R '' (W : Set V.V))

def act {R : Type} [CommRing R] [Algebra F R] (g : HA R hc.sig V.gram) (y : Fin V.rank → R ⊗[F] E) :
    Fin V.rank → R ⊗[F] E :=
  ((HA.mat R hc.sig V.gram g : GL (Fin V.rank) (R ⊗[F] E)) : Matrix (Fin V.rank) (Fin V.rank) (R ⊗[F] E)) *ᵥ y

section Act
variable {R : Type} [CommRing R] [Algebra F R]

theorem act_one (y : Fin V.rank → R ⊗[F] E) : act hc V (1 : HA R hc.sig V.gram) y = y :=
  Matrix.one_mulVec y

theorem act_mul (g h : HA R hc.sig V.gram) (y : Fin V.rank → R ⊗[F] E) :
    act hc V (g * h) y = act hc V g (act hc V h y) := (Matrix.mulVec_mulVec _ _ _).symm

theorem act_sub (g : HA R hc.sig V.gram) (y z : Fin V.rank → R ⊗[F] E) :
    act hc V g (y - z) = act hc V g y - act hc V g z := Matrix.mulVec_sub _ _ _

theorem act_inv (g : HA R hc.sig V.gram) (y : Fin V.rank → R ⊗[F] E) :
    act hc V g⁻¹ (act hc V g y) = y := by rw [← act_mul, inv_mul_cancel, act_one]

def stabSet (S : Set (Fin V.rank → R ⊗[F] E)) : Subgroup (HA R hc.sig V.gram) where
  carrier := {g | ∀ y, y ∈ S ↔ act hc V g y ∈ S}
  one_mem' := fun y => by rw [act_one]
  mul_mem' := fun {a b} ha hb y => by rw [act_mul]; exact (hb y).trans (ha _)
  inv_mem' := fun {a} ha y => by
    have := ha (act hc V a⁻¹ y)
    rw [← act_mul, mul_inv_cancel, act_one] at this
    exact this.symm

end Act

def latLoc (v : HeightOneSpectrum (𝓞 F)) : AddSubgroup (Fin V.rank → Fv F v ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x ∈ V.L0,
    y = fun i => a ⊗ₜ[F] V.frame.repr x i}

def hypLoc (v : HeightOneSpectrum (𝓞 F)) : Subgroup (GLoc hc V v) :=
  stabSet hc V (latLoc (F := F) V v : Set _)

def hypOff (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (GFin hc V) :=
  (⨅ v ∈ S, (projLoc hc V v).ker) ⊓ ⨅ v, ⨅ (_ : v ∉ S), (hypLoc hc V v).comap (projLoc hc V v)

def perp (W : Submodule E V.V) : Submodule E V.V := ⨅ w ∈ W, LinearMap.ker (V.hT w)

def IsIsotropic (W : Submodule E V.V) : Prop := W ≠ ⊥ ∧ W ≤ perp V W

def parab (R : Type) [CommRing R] [Algebra F R] (W : Submodule E V.V) : Subgroup (HA R hc.sig V.gram) :=
  stabSet hc V (extSub (F := F) V R W : Set _)

def unipRad (R : Type) [CommRing R] [Algebra F R] (W : Submodule E V.V) :
    Subgroup (HA R hc.sig V.gram) where
  carrier := {g | (∀ y ∈ extSub (F := F) V R W, act hc V g y = y) ∧
    ∀ y ∈ extSub (F := F) V R (perp V W), act hc V g y - y ∈ extSub (F := F) V R W}
  one_mem' := ⟨fun y _ => act_one hc V y, fun y _ => by rw [act_one, sub_self]; exact zero_mem _⟩
  mul_mem' := fun {a b} ha hb => ⟨fun y hy => by rw [act_mul, hb.1 y hy, ha.1 y hy], fun y hy => by
    have e : act hc V (a * b) y - y = (act hc V b y - y) + (act hc V a y - y) := by
      rw [← ha.1 _ (hb.2 y hy), act_sub, act_mul]; abel
    rw [e]; exact add_mem (hb.2 y hy) (ha.2 y hy)⟩
  inv_mem' := fun {a} ha => by
    have h1 : ∀ y ∈ extSub (F := F) V R W, act hc V a⁻¹ y = y := fun y hy => by
      conv_lhs => rw [← ha.1 y hy]
      exact act_inv hc V a y
    refine ⟨h1, fun y hy => ?_⟩
    have e : act hc V a⁻¹ y - y = -(act hc V a y - y) := by
      rw [← h1 _ (ha.2 y hy), act_sub, act_inv]; abel
    rw [e]; exact neg_mem (ha.2 y hy)

def unipRat (W : Submodule E V.V) : Subgroup (unipRad hc V (AF F) W) :=
  (ratPts hc V).subgroupOf (unipRad hc V (AF F) W)

def constTerm (W : Submodule E V.V) (μ : Measure (unipRad hc V (AF F) W))
    (𝓕 : Set (unipRad hc V (AF F) W)) (f : GA hc V → ℂ) (g : GA hc V) : ℂ :=
  ∫ n in 𝓕, f ((n : GA hc V) * g) ∂μ

def constTermZero (W : Submodule E V.V) : Submodule ℂ (GA hc V → ℂ) where
  carrier := {f | ∀ μ : Measure (unipRad hc V (AF F) W), μ.IsHaarMeasure →
    ∀ 𝓕, IsFundamentalDomain (unipRat hc V W) 𝓕 μ → ∀ g : GA hc V,
      IntegrableOn (fun n : unipRad hc V (AF F) W => f ((n : GA hc V) * g)) 𝓕 μ ∧
        constTerm hc V W μ 𝓕 f g = 0}
  zero_mem' := fun μ _ 𝓕 _ g => ⟨integrable_zero _ _ _, by simp [constTerm]⟩
  add_mem' := fun {a b} ha hb μ hμ 𝓕 h𝓕 g => by
    obtain ⟨i1, z1⟩ := ha μ hμ 𝓕 h𝓕 g
    obtain ⟨i2, z2⟩ := hb μ hμ 𝓕 h𝓕 g
    refine ⟨i1.add i2, ?_⟩
    unfold constTerm at *
    simp only [Pi.add_apply]
    rw [integral_add i1 i2, z1, z2, add_zero]
  smul_mem' := fun c a ha μ hμ 𝓕 h𝓕 g => by
    obtain ⟨i1, z1⟩ := ha μ hμ 𝓕 h𝓕 g
    refine ⟨Integrable.smul c i1, ?_⟩
    unfold constTerm at *
    simp only [Pi.smul_apply]
    rw [integral_smul, z1, smul_zero]

def cuspidal : Submodule ℂ (GA hc V → ℂ) :=
  ⨅ W : Submodule E V.V, ⨅ (_ : IsIsotropic V W), constTermZero hc V W

end Groups

section Embedding

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E)

theorem hT_coord (V : HSpace E) (x y : V.V) :
    V.hT x y = ∑ i, ∑ j, star (V.frame.repr x i) * V.gram i j * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    HSpace.gram, RingHom.id_apply, starRingEnd_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring

theorem gram_det_isUnit (V : HSpace E) : IsUnit V.gram.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hy : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    rw [hT_coord]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun hz i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    have e : ∀ j, V.frame.repr (V.frame.equivFun.symm v) j = v j := fun j => by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp only [e, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  exact hv (V.frame.equivFun.symm.map_eq_zero_iff.1 hy)

theorem cT_gram (V : HSpace E) : cT (hc.sig : E →+* E) V.gram = V.gram := by
  ext i j
  exact V.herm.eq (V.frame j) (V.frame i)

variable (B A : HSpace E) (ι : B.V →ₗ[E] A.V)

def embMat : Matrix (Fin A.rank) (Fin B.rank) E := LinearMap.toMatrix B.frame A.frame ι

def projMat : Matrix (Fin B.rank) (Fin A.rank) E :=
  B.gram⁻¹ * cT (hc.sig : E →+* E) (embMat B A ι) * A.gram

theorem embMat_isom (h : HSpace.IsIsomEmb B A ι) :
    cT (hc.sig : E →+* E) (embMat B A ι) * A.gram * embMat B A ι = B.gram := by
  ext i j
  have := hT_coord A (ι (B.frame i)) (ι (B.frame j))
  rw [h] at this
  rw [HSpace.gram, this, Finset.sum_comm]
  simp only [Matrix.mul_apply, cT, embMat, Matrix.transpose_apply, Matrix.map_apply,
    LinearMap.toMatrix_apply, Finset.sum_mul]
  rfl

theorem gram_projMat : cT (hc.sig : E →+* E) (embMat B A ι) * A.gram = B.gram * projMat hc B A ι := by
  rw [projMat, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_det_isUnit B),
    Matrix.one_mul]

theorem projMat_embMat (h : HSpace.IsIsomEmb B A ι) : projMat hc B A ι * embMat B A ι = 1 := by
  rw [projMat, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ _), embMat_isom hc B A ι h,
    Matrix.nonsing_inv_mul _ (gram_det_isUnit B)]

theorem cT_projMat : cT (hc.sig : E →+* E) (projMat hc B A ι) * B.gram = A.gram * embMat B A ι := by
  have h := congrArg (cT (hc.sig : E →+* E)) (gram_projMat hc B A ι)
  rw [cT_mul, cT_mul, cT_gram, cT_gram] at h
  rw [← h]
  congr 1
  ext i j
  exact star_star _

def embH (h : HSpace.IsIsomEmb B A ι) (R : Type) [CommRing R] [Algebra F R] :
    HA R hc.sig B.gram →* HA R hc.sig A.gram :=
  have hs : ∀ x : E, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig (inclR R x) = inclR R ((hc.sig : E →+* E) x) :=
    fun _ => rfl
  embU (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig) (JR R B.gram) (JR R A.gram) ((embMat B A ι).map (inclR (F := F) R))
    ((projMat hc B A ι).map (inclR (F := F) R))
    (by rw [← Matrix.map_mul, projMat_embMat hc B A ι h, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [cT_map _ _ _ hs, JR, JR, ← Matrix.map_mul, ← Matrix.map_mul, cT_projMat])
    (by rw [cT_map _ _ _ hs, JR, JR, ← Matrix.map_mul, ← Matrix.map_mul, gram_projMat])

def embRat (h : HSpace.IsIsomEmb B A ι) : GRat hc B →* GRat hc A :=
  embU (hc.sig : E →+* E) B.gram A.gram (embMat B A ι) (projMat hc B A ι) (projMat_embMat hc B A ι h)
    (cT_projMat hc B A ι) (gram_projMat hc B A ι)

def embA (h : HSpace.IsIsomEmb B A ι) : GA hc B →* GA hc A := embH hc B A ι h (AF F)

end Embedding

section Claims

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (V : HSpace E)

theorem ratPts_eq : ratPts hc V = HFinIn (AF F) hc.sig V.gram := by
  ext g
  constructor
  · rintro ⟨γ, rfl⟩; exact ⟨γ.1, γ.2, rfl⟩
  · rintro ⟨γ, hγ, e⟩; exact ⟨⟨γ, hγ⟩, Subtype.ext e⟩

end Claims

section Host

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (V : TH.HSp D)

end Host

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups
