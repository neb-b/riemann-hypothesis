module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.Bundle0021
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0020

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge
section
noncomputable section

namespace PI.MassDataKppVolLemmas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField IsDedekindDomain Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix
open Formalism.MainNotions.S (AutInst)

variable (I : AutInst) (hb : AdBridgeIso I)

def tf (x : I.Gf) : HA (Af I.F) I.cm.sig I.J := (splitA I.cm.sig I.J (toHA I hb (1, x))).2

def tfHom : I.Gf →* HA (Af I.F) I.cm.sig I.J :=
  (MonoidHom.snd _ _).comp ((splitA I.cm.sig I.J).comp
    ((toHA I hb : I.GA →* HAd I).comp (MonoidHom.inr _ _)))

theorem Bridge_tfHom_apply (x : I.Gf) : tfHom I hb x = tf I hb x := rfl

def swapE : I.E ⊗[I.F] Af I.F ≃ₐ[I.F] Af I.F ⊗[I.F] I.E := Algebra.TensorProduct.comm I.F I.E (Af I.F)

theorem Bridge_tens_eq (t : AF I.F ⊗[I.F] I.E) :
    tensMap (E := I.E) (sndA I.F) t = swapE I (tauF I t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [tensMap, tauF, swapE, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add s u hs hu => rw [map_add (f := _), map_add (f := _), map_add (f := _), hs, hu]


variable {I} in
theorem Bridge_HA_ext {R : Type} [CommRing R] [Algebra I.F R] (g h : HA R I.cm.sig I.J)
    (e : ((HA.mat R I.cm.sig I.J g : GL (Fin I.n) (R ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) (R ⊗[I.F] I.E)) =
      ((HA.mat R I.cm.sig I.J h : GL (Fin I.n) (R ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) (R ⊗[I.F] I.E))) :
    g = h := Subtype.ext (Units.ext e)

theorem Bridge_mat (x : I.Gf) :
    ((HA.mat (Af I.F) I.cm.sig I.J (tf I hb x) : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) _) = (I.fmat x).map (swapE I) := by
  have hB : I.fmat x = (hmat I (toHA I hb (1, x))).map (tauF I) := (hb.choose_spec (1, x)).2
  have h1 : ((HA.mat (Af I.F) I.cm.sig I.J (tf I hb x) : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) =
      (hmat I (toHA I hb (1, x))).map (tensMap (E := I.E) (sndA I.F)) := rfl
  rw [h1, hB, Matrix.map_map]
  ext i j
  exact Bridge_tens_eq I _

theorem Bridge_tf_injective : Function.Injective (tf I hb) := by
  intro x y hxy
  have h1 : (I.fmat x).map (swapE I) = (I.fmat y).map (swapE I) := by
    rw [← Bridge_mat I hb x, ← Bridge_mat I hb y, hxy]
  have h2 : I.fmat x = I.fmat y := by
    ext i j
    exact (swapE I).injective (congrFun (congrFun h1 i) j)
  exact Subtype.ext (Units.ext h2)

theorem Bridge_tf_surjective : Function.Surjective (tf I hb) := by
  intro h
  let φ : Af I.F ⊗[I.F] I.E →+* I.E ⊗[I.F] Af I.F := (swapE I).symm.toAlgHom.toRingHom
  have hσ : φ.comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig) = (Formalism.UG.sigR I.cm.sig (Af I.F)).comp φ := by
    refine RingHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [φ, swapE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR]
    | add s u hs hu => simp only [map_add (f := _)] at hs hu ⊢; rw [hs, hu]
  have hJ : (JR (Af I.F) I.J).map φ = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    ext i j
    simp [φ, swapE, JR, inclR, Formalism.UG.inclE]
  have hmem := Formalism.UG.P.bc_mem _ _ φ hσ (JR (Af I.F) I.J) (HA.mat (Af I.F) I.cm.sig I.J h) h.2
  rw [hJ] at hmem
  let x : I.Gf := ⟨Formalism.UG.bc φ (HA.mat (Af I.F) I.cm.sig I.J h), hmem⟩
  refine ⟨x, Bridge_HA_ext (tf I hb x) h ?_⟩
  rw [Bridge_mat]
  ext i j
  change swapE I (φ _) = _
  first
    | exact (swapE I).apply_symm_apply _
    | simp [φ]

theorem Bridge_mem_Kf_iff (x : I.Gf) :
    tf I hb x ∈ Kf I.cm.sig I.J (I.L : Set (Fin I.n → I.E)) ↔ x ∈ I.Kset := by
  have hF := adelic_compact_finite_places I (toHA I hb (1, x))
  have hx : I.fmat x = ofHAFin I (toHA I hb (1, x)) := (toHA_isBridge I hb (1, x)).2
  have hK : x ∈ I.Kset ↔ ∀ y, y ∈ I.Lf ↔ ofHAFin I (toHA I hb (1, x)) *ᵥ y ∈ I.Lf := by
    rw [← hx]; exact Iff.rfl
  rw [hK, hF, Kf, Subgroup.mem_iInf]
  exact Iff.rfl

end PI.MassDataKppVolLemmas
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocLocGLInvVal
section
noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct Matrix

section Gen

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def locM (e : A) (M : Matrix n n A) : Matrix n n A := 1 + e • (M - 1)

theorem Loc_locM_one (e : A) : locM e (1 : Matrix n n A) = 1 := by
  simp [locM]

theorem Loc_locM_zero (M : Matrix n n A) : locM (0 : A) M = 1 := by
  simp [locM]

theorem Loc_locM_one' (M : Matrix n n A) : locM (1 : A) M = M := by
  simp [locM]

theorem Loc_locM_add (a b : A) (hab : a * b = 0) (M : Matrix n n A) :
    locM a M * locM b M = locM (a + b) M := by
  simp only [locM, add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hab, zero_smul, add_zero, add_smul]
  abel

theorem Loc_locM_mul (e : A) (he : e * e = e) (M N : Matrix n n A) :
    locM e (M * N) = locM e M * locM e N := by
  have h : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  simp only [locM, h, add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, he, smul_add]
  abel

theorem Loc_locM_split (e : A) (he : e * e = e) (M : Matrix n n A) :
    locM e M * locM (1 - e) M = M := by
  rw [Loc_locM_add e (1 - e) (by rw [mul_sub, mul_one, he, sub_self]), show e + (1 - e) = (1 : A) by ring,
    Loc_locM_one']

theorem Loc_locM_sub_one (e : A) (M : Matrix n n A) (v : n → A) :
    (locM e M - 1) *ᵥ v = e • ((M - 1) *ᵥ v) := by
  rw [locM, add_sub_cancel_left]
  first
    | exact Matrix.smul_mulVec _ _ _
    | (ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])

theorem Loc_locM_map {B : Type} [CommRing B] (f : A →+* B) (e : A) (M : Matrix n n A) :
    (locM e M).map f = locM (f e) (M.map f) := by
  ext i j
  simp only [locM, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    smul_eq_mul]
  split_ifs <;> simp [map_add (f := _), map_mul, map_sub]

theorem Loc_cT (σ : A →+* A) (e : A) (hσ : σ e = e) (M : Matrix n n A) :
    Formalism.UG.cT σ (locM e M) = locM e (Formalism.UG.cT σ M) := by
  unfold Formalism.UG.cT
  rw [Loc_locM_map, hσ]
  simp [locM, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one]

theorem Loc_locM_unitary (σ : A →+* A) (e : A) (he : e * e = e) (hσ : σ e = e) (J M : Matrix n n A)
    (hM : Formalism.UG.cT σ M * J * M = J) : Formalism.UG.cT σ (locM e M) * J * locM e M = J := by
  rw [Loc_cT σ e hσ]
  set N := Formalism.UG.cT σ M with hN
  have key : (N - 1) * J + J * (M - 1) + (N - 1) * J * (M - 1) = 0 := by
    have h0 : N * J * M - J = 0 := sub_eq_zero.mpr hM
    rw [← h0]; noncomm_ring
  calc (locM e N) * J * locM e M = J + e • ((N - 1) * J + J * (M - 1) + (N - 1) * J * (M - 1)) := by
        simp only [locM, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul, he,
          smul_add, Matrix.mul_assoc]
        abel
    _ = J := by rw [key, smul_zero, add_zero]

def locGL (e : A) (he : e * e = e) : GL n A →* GL n A where
  toFun g := ⟨locM e g, locM e ↑g⁻¹, by rw [← Loc_locM_mul e he, Units.mul_inv, Loc_locM_one],
    by rw [← Loc_locM_mul e he, Units.inv_mul, Loc_locM_one]⟩
  map_one' := Units.ext (Loc_locM_one e)
  map_mul' g h := Units.ext (Loc_locM_mul e he _ _)

theorem Loc_locGL_val (e : A) (he : e * e = e) (g : GL n A) :
    ((locGL e he g : GL n A) : Matrix n n A) = locM e (g : Matrix n n A) := rfl

end Gen

end PI.MassDataKppVolLemmas
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.MassDataKppVolOf
section
noncomputable section

namespace PI.MassDataKppVolLemmas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped ENNReal

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

abbrev lamS : Set (Fin X.B.I.n → X.B.I.E) := (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

abbrev KfS : Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := Kf X.B.I.cm.sig X.B.I.J (lamS X)

def KppS : Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := Subgroup.closure (levelUnitary X hb)

def gIdx : ℕ := (KppS X hb).relIndex (KfS X)

def KvS (p : TypX X) : Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) :=
  Subgroup.closure (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1)

def KppvS (p : TypX X) : Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) :=
  Subgroup.closure (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)

def lIdx (p : TypX X) : ℕ := (KppvS X hb p).relIndex (KvS X p)

def GlobIdx : Prop :=
  gIdx X hb ≠ 0 → X.measG.μGf (KfS X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) =
    (gIdx X hb : ℝ≥0∞) * X.measG.μGf (levelUnitary X hb)

def LocIdx : Prop :=
  ∀ p : TypX X, lIdx X hb p ≠ 0 → X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1) =
    (lIdx X hb p : ℝ≥0∞) * X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)

def LocPos : Prop :=
  ∀ p : TypX X, 0 < X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1) ∧
    X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1) < ⊤ ∧ lIdx X hb p ≠ 0

def IdxProd : Prop := gIdx X hb = ∏ p : TypX X, lIdx X hb p

def GlobIdxAll : Prop := ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb →
  X.LevelSubgroupNormalized → GlobIdx X hb
def LocIdxAll : Prop := ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb →
  X.LevelSubgroupNormalized → LocIdx X hb
def LocPosAll : Prop := ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb →
  X.LevelSubgroupNormalized → LocPos X hb
def IdxProdAll : Prop := ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb →
  X.LevelSubgroupNormalized → IdxProd X hb

theorem Steps_bOf_μKpp (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn) :
    (bOf X hb hK FdN FdN' u u' X0 L A).μKpp =
      (X.measG.μGf (KfS X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))).toReal /
        (∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1)).toReal) *
        ∏ p : TypX X, (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal := rfl

theorem Steps_main (h1 : GlobIdx X hb) (h2 : LocIdx X hb) (h3 : LocPos X hb) (h4 : IdxProd X hb) :
    (X.measG.μGf (KfS X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))).toReal /
        (∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1)).toReal) *
        ∏ p : TypX X, (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal =
      (X.measG.μGf (levelUnitary X hb)).toReal := by
  have hne : ∀ p : TypX X,
      (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal ≠ 0 := fun p =>
    (ENNReal.toReal_pos (h3 p).1.ne' (h3 p).2.1.ne).ne'
  have hg : gIdx X hb ≠ 0 := by
    rw [h4]
    exact Finset.prod_ne_zero_iff.mpr fun p _ => (h3 p).2.2
  have hprod : ∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1)).toReal =
      (gIdx X hb : ℝ) *
        ∏ p : TypX X, (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal := by
    rw [h4, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [h2 p (h3 p).2.2, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hP : ∏ p : TypX X,
      (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ => hne p
  have hG : (gIdx X hb : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  rw [hprod, h1 hg, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_div_mul_left _ _ hG,
    div_mul_cancel₀ _ hP]

theorem massDataKppVol_of (h1 : GlobIdxAll) (h2 : LocIdxAll) (h3 : LocPosAll) (h4 : IdxProdAll) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X))
      (A : AnIn), KppVolAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hyp
  rw [Steps_bOf_μKpp X hb hK FdN FdN' u u' X0 L A]
  exact Steps_main X hb (h1 X hb hK hyp.1 hyp.2.1) (h2 X hb hK hyp.1 hyp.2.1)
    (h3 X hb hK hyp.1 hyp.2.1) (h4 X hb hK hyp.1 hyp.2.1)

end PI.MassDataKppVolLemmas
end
end

