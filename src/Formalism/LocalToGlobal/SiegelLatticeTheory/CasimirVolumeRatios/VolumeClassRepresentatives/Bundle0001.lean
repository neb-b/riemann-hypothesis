module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Formalism.LocalRingCardinality.Bundle0003

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ZsCovFin
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.L2.S.S7.ZsCovFin

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

abbrev swp : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E ≃ₐ[F] E ⊗[F] Formalism.MainNotions.S.Af F :=
  Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E

theorem intAf_one : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ intAf F := fun v => by
  show evalV F v 1 ∈ _
  rw [map_one]; exact one_mem _

theorem intAf_mul {a b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := fun v => by
  show evalV F v (a * b) ∈ _
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem mul_mem_latHat (L : Set (Fin n → E)) (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)
    (hc : ∀ a ∈ intAf F, ∀ x ∈ L, (fun i => c * (a ⊗ₜ[F] x i)) ∈ latHat F E L)
    {w : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E} (hw : w ∈ latHat F E L) : (fun i => c * w i) ∈ latHat F E L := by
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact hc a ha x hx
  | zero =>
    convert (latHat F E L).zero_mem using 1
    funext i; simp
  | add y z _ _ hy hz =>
    convert (latHat F E L).add_mem hy hz using 1
    funext i; simp [mul_add]
  | neg y _ hy =>
    convert (latHat F E L).neg_mem hy using 1
    funext i; simp [mul_neg]

theorem mem_latHat_iff (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :
    y ∈ latHat F E (L : Set (Fin n → E)) ↔ (fun i => swp (y i)) ∈ lamAf (F := F) L := by
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have hmem : ((1 : E) ⊗ₜ[F] a) ∈ IntAf F E :=
        Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩)
      have hx' : (fun i => Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (x i)) ∈ lamAf (F := F) L :=
        Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      have := (lamAf (F := F) L).smul_mem (⟨_, hmem⟩ : IntAf F E) hx'
      convert this using 1
      funext i
      simp [swp, Formalism.UG.inclE, Subring.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
    | zero =>
      convert (lamAf (F := F) L).zero_mem using 1
      funext i; simp
    | add y z _ _ hy hz =>
      convert (lamAf (F := F) L).add_mem hy hz using 1
      funext i; simp
    | neg y _ hy =>
      convert (lamAf (F := F) L).neg_mem hy using 1
      funext i; simp
  · intro hz

    let R : Subring (E ⊗[F] Formalism.MainNotions.S.Af F) :=
      { carrier := {r | ∀ w ∈ latHat F E (L : Set (Fin n → E)), (fun i => swp.symm r * w i) ∈ latHat F E (L : Set (Fin n → E))}
        mul_mem' := fun {r s} hr hs w hw => by
          have := hr _ (hs w hw)
          simpa [map_mul, mul_assoc] using this
        one_mem' := fun w hw => by simpa using hw
        add_mem' := fun {r s} hr hs w hw => by
          convert (latHat F E (L : Set (Fin n → E))).add_mem (hr w hw) (hs w hw) using 1
          funext i; simp [map_add (f := _), add_mul]
        zero_mem' := fun w _ => by
          convert (latHat F E (L : Set (Fin n → E))).zero_mem using 1
          funext i; simp
        neg_mem' := fun {r} hr w hw => by
          convert (latHat F E (L : Set (Fin n → E))).neg_mem (hr w hw) using 1
          funext i; simp [map_neg, neg_mul] }
    have hIR : IntAf F E ≤ R := by
      refine (Subring.closure_le).2 ?_
      rintro r (⟨⟨o, ho⟩, rfl⟩ | ⟨⟨a', ha'⟩, rfl⟩)
      · intro w hw
        refine mul_mem_latHat _ _ ?_ hw
        intro a ha x hx
        obtain ⟨o', rfl⟩ := ho
        refine AddSubgroup.subset_closure ⟨a, ha, o' • x, L.smul_mem o' hx, ?_⟩
        funext i
        simp [swp, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
      · intro w hw
        refine mul_mem_latHat _ _ ?_ hw
        intro a ha x hx
        refine AddSubgroup.subset_closure ⟨a' * a, intAf_mul (fun v => ha' v) ha, x, hx, ?_⟩
        funext i
        simp [swp, Algebra.TensorProduct.tmul_mul_tmul]
    have key : ∀ z ∈ lamAf (F := F) L, (fun i => swp.symm (z i)) ∈ latHat F E (L : Set (Fin n → E)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨1, intAf_one, x, x.2, ?_⟩
        funext i
        simp [swp, Formalism.UG.inclE]
      | zero =>
        convert (latHat F E (L : Set (Fin n → E))).zero_mem using 1
        funext i; simp
      | add z z' _ _ hz hz' =>
        convert (latHat F E (L : Set (Fin n → E))).add_mem hz hz' using 1
        funext i; simp
      | smul r z _ hz =>
        have := hIR r.2 _ hz
        simpa [Subring.smul_def, map_mul] using this
    have := key _ hz
    simpa using this

theorem stab_iff (L : Submodule (𝓞 E) (Fin n → E)) (M : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E))
    (M' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) (hM : M' = M.map swp) :
    (∀ y, y ∈ latHat F E (L : Set (Fin n → E)) ↔ Matrix.mulVec M y ∈ latHat F E (L : Set (Fin n → E))) ↔
      ∀ z, z ∈ lamAf (F := F) L ↔ Matrix.mulVec M' z ∈ lamAf (F := F) L := by
  subst hM
  have hmv : ∀ y : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E,
      Matrix.mulVec (M.map swp) (fun i => swp (y i)) = fun i => swp ((Matrix.mulVec M y) i) := fun y => by
    funext i
    exact (RingHom.map_mulVec (swp (F := F) (E := E)).toRingEquiv.toRingHom M y i).symm
  constructor
  · intro h z
    obtain ⟨y, rfl⟩ : ∃ y : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E, (fun i => swp (y i)) = z :=
      ⟨fun i => swp.symm (z i), by funext i; simp⟩
    rw [hmv, ← mem_latHat_iff, ← mem_latHat_iff]
    exact h y
  · intro h y
    rw [mem_latHat_iff, mem_latHat_iff, ← hmv]
    exact h _

end Gen

section Brg

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem hermitianSpaceBaseLattice_eq_frameLattice : L0c D V = ((Formalism.IndefR.Eqv.UI.Lv D V : Submodule _ _) : Set (Fin V.rank → D.host.E)) := by
  ext x
  exact (Formalism.IndefR.Eqv.UI.mem_Lv D V x).symm

theorem finCond_brg (fr : Formalism.IndefR.Eqv.UI.Frames D V) (hΛ : fr.Λ = Formalism.IndefR.Eqv.UI.Lv D V)
    (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) :
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      (finMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.UI.brg fr x)).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)) ↔
    x.2 ∈ (Formalism.IndefR.Eqv.UI.instV fr).Kset := by
  have hfin := Formalism.IndefR.Eqv.finE_brg fr x
  have hM : ((x.2.1 : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).val : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) =
      (finMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.UI.brg fr x)).map swp := by
    have := congrArg (fun g : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => g.val) hfin
    exact this.symm
  have hL : L0c D V = ((fr.Λ : Submodule _ _) : Set (Fin V.rank → D.host.E)) := by
    rw [hΛ]; exact hermitianSpaceBaseLattice_eq_frameLattice
  rw [hL]
  exact stab_iff fr.Λ _ _ hM

end Brg

end Formalism.L2.S.S7.ZsCovFin
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ZsCovInf
section
noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

namespace Formalism.L2.S.S7.ZsCovInf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Grp

variable {n : ℕ} (ε : Fin n → Bool)

theorem Jm_det : (Formalism.REAL.Jm ε).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (Formalism.REAL.Jm_mul_self ε)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem det_ne_of_inUJ {C : Matrix (Fin n) (Fin n) ℂ} (h : Cᴴ * Formalism.REAL.Jm ε * C = Formalism.REAL.Jm ε) : C.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact Jm_det ε this.symm

def ofInUJ {C : Matrix (Fin n) (Fin n) ℂ} (h : Cᴴ * Formalism.REAL.Jm ε * C = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨Matrix.nonsingInvUnit C (Ne.isUnit (det_ne_of_inUJ ε h)), h⟩

theorem umat_mul (g h : Formalism.REAL.UJ ε) :
    PI.CdHaarScale.umat (g * h) = PI.CdHaarScale.umat g * PI.CdHaarScale.umat h := rfl

theorem umat_ext {g h : Formalism.REAL.UJ ε} (e : PI.CdHaarScale.umat g = PI.CdHaarScale.umat h) : g = h :=
  Subtype.ext (Units.ext e)

theorem map_conj_muG (c : Formalism.REAL.UJ ε) : (Formalism.REAL.muG ε).map (fun g => c * g * c⁻¹) = Formalism.REAL.muG ε := by
  have : (Formalism.REAL.muG ε).IsMulRightInvariant := Formalism.IndefR.Eqv.uJ_rightInv ε _ inferInstance
  have h1 : (fun g : Formalism.REAL.UJ ε => c * g * c⁻¹) = (fun g => g * c⁻¹) ∘ (fun g => c * g) := rfl
  have hm1 : Measurable (fun g : Formalism.REAL.UJ ε => c * g) := measurable_const_mul c
  have hm2 : Measurable (fun g : Formalism.REAL.UJ ε => g * c⁻¹) := measurable_mul_const c⁻¹
  rw [h1, ← Measure.map_map hm2 hm1, map_mul_left_eq_self, map_mul_right_eq_self]

end Grp

section Frame

variable {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)

include h1 h2 in
theorem signs_eq : (fun i => (e.symm i).isLeft) = ε := by
  funext i
  obtain ⟨s, rfl⟩ := e.surjective i
  rcases s with s | s
  · simp [h1]
  · simp [h2]


include h1 h2 in
theorem sq_inUJ {C : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ} (hC : Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.REAL.Jm ε) :
    (C.submatrix e.symm id)ᴴ * Formalism.REAL.Jm ε * C.submatrix e.symm id = Formalism.REAL.Jm ε := by
  have := Formalism.IndefR.Eqv.MF.sq_gram e.symm C
  rw [signs_eq e h1 h2] at this
  rw [this, hC]

theorem submatrix_inj {m : Type} {X Y : Matrix (Fin P ⊕ Fin Q) m ℂ}
    (h : X.submatrix e.symm id = Y.submatrix e.symm id) : X = Y := by
  have := congrArg (fun Z : Matrix (Fin n) m ℂ => Z.submatrix e id) h
  simpa using this

end Frame

section Cond

variable {D : D7} {V : HSp D} (fr : Formalism.IndefR.Eqv.UI.Frames D V) {P Q : ℕ}

theorem frame_C (v : InfinitePlace D.host.F) {A : Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ}
    (hA : Aᴴ * Formalism.UG.Jpq P Q * A = V.gram.map (embOf D ((Formalism.L2.Host.tauPl D).symm v))) :
    (A * fr.P v)ᴴ * Formalism.UG.Jpq P Q * (A * fr.P v) = Formalism.REAL.Jm (fr.ε v) := by
  rw [Matrix.conjTranspose_mul]
  have h := fr.spec v
  calc (fr.P v)ᴴ * Aᴴ * Formalism.UG.Jpq P Q * (A * fr.P v) = (fr.P v)ᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) * fr.P v := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (fr.ε v) := by rw [hA]; exact h

def cEl (v : InfinitePlace D.host.F) {A : Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ}
    (hA : Aᴴ * Formalism.UG.Jpq P Q * A = V.gram.map (embOf D ((Formalism.L2.Host.tauPl D).symm v)))
    (e : Fin P ⊕ Fin Q ≃ Fin V.rank) (h1 : ∀ i, fr.ε v (e (Sum.inl i)) = true)
    (h2 : ∀ j, fr.ε v (e (Sum.inr j)) = false) : Formalism.REAL.UJ (fr.ε v) :=
  ofInUJ (fr.ε v) (sq_inUJ e h1 h2 (frame_C fr v hA))

theorem infCond (v : InfinitePlace D.host.F) {A : Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ}
    (hA : Aᴴ * Formalism.UG.Jpq P Q * A = V.gram.map (embOf D ((Formalism.L2.Host.tauPl D).symm v)))
    (e : Fin P ⊕ Fin Q ≃ Fin V.rank) (h1 : ∀ i, fr.ε v (e (Sum.inl i)) = true)
    (h2 : ∀ j, fr.ε v (e (Sum.inr j)) = false) (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (B : Set (UpqT P Q)) :
    (∃ b ∈ B, UpqT.mat b * A = A * infMat D.sp.cm.sig V.gram
        (Formalism.IndefR.Eqv.thetaC D ((Formalism.L2.Host.tauPl D).symm v)) (Formalism.IndefR.Eqv.UI.brg fr x)) ↔
      (x.1 v : Formalism.REAL.UJ (fr.ε v)) ∈ (fun g : Formalism.REAL.UJ (fr.ε v) => cEl fr v hA e h1 h2 * g * (cEl fr v hA e h1 h2)⁻¹) ⁻¹'
        (PI.UnitaryGroupMassFormula.CdHaarScale.Main.phi e h1 h2 '' B) := by
  set c := cEl fr v hA e h1 h2 with hc
  set xv : Formalism.REAL.UJ (fr.ε v) := x.1 v with hxv
  have hX : infMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.thetaC D ((Formalism.L2.Host.tauPl D).symm v))
      (Formalism.IndefR.Eqv.UI.brg fr x) = fr.P v * Formalism.IndefR.Eqv.uM fr x v * (fr.P v)⁻¹ := by
    have h := Formalism.IndefR.Eqv.infMat_brg fr x ((Formalism.L2.Host.tauPl D).symm v)
    rw [Equiv.apply_symm_apply] at h
    exact h
  have hu := Formalism.IndefR.Eqv.P_isUnit_det fr v
  set u := Formalism.IndefR.Eqv.uM fr x v with hudef
  set C := A * fr.P v with hCdef
  have step1 : ∀ b : UpqT P Q, UpqT.mat b * A = A * (fr.P v * u * (fr.P v)⁻¹) ↔ UpqT.mat b * C = C * u := by
    intro b
    constructor
    · intro h
      rw [hCdef, ← Matrix.mul_assoc, h, Matrix.mul_assoc A, Matrix.mul_assoc (fr.P v * u),
        Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, ← Matrix.mul_assoc]
    · intro h
      calc UpqT.mat b * A = UpqT.mat b * C * (fr.P v)⁻¹ := by
            rw [hCdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
        _ = C * u * (fr.P v)⁻¹ := by rw [h]
        _ = A * (fr.P v * u * (fr.P v)⁻¹) := by rw [hCdef]; simp only [Matrix.mul_assoc]
  have hcm : PI.CdHaarScale.umat c = C.submatrix e.symm id := rfl
  have hxm : PI.CdHaarScale.umat xv = u := rfl
  have step2 : ∀ b : UpqT P Q, UpqT.mat b * C = C * u ↔ PI.UnitaryGroupMassFormula.CdHaarScale.Main.phi e h1 h2 b * c = c * xv := by
    intro b
    have hs1 : (UpqT.mat b * C).submatrix e.symm id =
        PI.CdHaarScale.umat (PI.UnitaryGroupMassFormula.CdHaarScale.Main.phi e h1 h2 b * c) := by
      rw [umat_mul, PI.UnitaryGroupMassFormula.CdHaarScale.Main.umat_phi, hcm, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    have hs2 : (C * u).submatrix e.symm id = PI.CdHaarScale.umat (c * xv) := by
      rw [umat_mul, hcm, hxm]
      ext i j
      simp [Matrix.mul_apply]
    constructor
    · intro h
      apply umat_ext
      rw [← hs1, ← hs2, h]
    · intro h
      apply submatrix_inj e
      rw [hs1, hs2, h]
  rw [hX]
  show _ ↔ c * xv * c⁻¹ ∈ PI.UnitaryGroupMassFormula.CdHaarScale.Main.phi e h1 h2 '' B
  rw [Set.mem_image]
  constructor
  · rintro ⟨b, hb, hbA⟩
    refine ⟨b, hb, ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    exact (step2 b).1 ((step1 b).1 hbA)
  · rintro ⟨b, hb, hbx⟩
    refine ⟨b, hb, (step1 b).2 ((step2 b).2 ?_)⟩
    rw [hbx, inv_mul_cancel_right]

theorem measAt (hcd : cdScaleTie D) {n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) (c : Formalism.REAL.UJ ε)
    (B : Set (UpqT P Q)) (hB : MeasurableSet B) :
    ((D.s.cdScale n ε : ENNReal) • Formalism.REAL.muG ε)
        ((fun g => c * g * c⁻¹) ⁻¹' (PI.UnitaryGroupMassFormula.CdHaarScale.Main.phi e h1 h2 '' B)) = D.cd.cd P Q B := by
  have hS : MeasurableSet (PI.UnitaryGroupMassFormula.CdHaarScale.Main.phi e h1 h2 '' B) :=
    (PI.UnitaryGroupMassFormula.CdHaarScale.Main.phi e h1 h2).toHomeomorph.measurableEmbedding.measurableSet_image.2 hB
  have hcm : Measurable (fun g : Formalism.REAL.UJ ε => c * g * c⁻¹) := (measurable_const_mul c).mul_const c⁻¹
  rw [Measure.smul_apply, ← Measure.map_apply hcm hS, map_conj_muG, ← Measure.smul_apply]
  rw [hcd n ε P Q e h1 h2 _ hS]
  have ht := PI.UnitaryGroupMassFormula.CdHaarScale.Main.tie_set e h1 h2 (PI.UnitaryGroupMassFormula.CdHaarScale.Main.phi e h1 h2 '' B)
  rw [Set.preimage_image_eq _ (PI.UnitaryGroupMassFormula.CdHaarScale.Main.phi e h1 h2).injective] at ht
  exact congrArg (D.cd.cd P Q) ht

end Cond

end Formalism.L2.S.S7.ZsCovInf
end
end

