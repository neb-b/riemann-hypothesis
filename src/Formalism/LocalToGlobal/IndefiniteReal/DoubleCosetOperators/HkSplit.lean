module

public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.HeckeCommuteOfCompatibility
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.UG

open scoped TensorProduct

namespace Formalism.IndefR.NX

section Ext

variable {S S' R : Type} [CommRing S] [CommRing S'] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def extM (ι : S →ₙ+* R) (A : Matrix n n S) : Matrix n n R := (1 - ι 1) • (1 : Matrix n n R) + A.map ι

theorem idem_mul (ι : S →ₙ+* R) (x : S) : ι 1 * ι x = ι x := by rw [← map_mul, one_mul]

theorem compl_mul (ι : S →ₙ+* R) (x : S) : (1 - ι 1) * ι x = 0 := by
  rw [sub_mul, one_mul, idem_mul, sub_self]

theorem map_mul_nu (ι : S →ₙ+* R) (A B : Matrix n n S) : (A * B).map ι = A.map ι * B.map ι := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

theorem compl_smul_map (ι : S →ₙ+* R) (A : Matrix n n S) : (1 - ι 1) • A.map ι = 0 := by
  ext i j; simp [compl_mul]

theorem extM_one (ι : S →ₙ+* R) : extM ι (1 : Matrix n n S) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [extM]
  · simp [extM, Matrix.one_apply, h]

theorem extM_mul (ι : S →ₙ+* R) (A B : Matrix n n S) : extM ι (A * B) = extM ι A * extM ι B := by
  have hc : (1 - ι 1) * (1 - ι 1) = 1 - ι 1 := by
    have h := idem_mul ι 1
    linear_combination h
  simp only [extM, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    compl_smul_map, smul_smul, hc, map_mul_nu, add_zero, zero_add]

def extHom (ι : S →ₙ+* R) : Matrix n n S →* Matrix n n R where
  toFun := extM ι
  map_one' := extM_one ι
  map_mul' := extM_mul ι

def extGL (ι : S →ₙ+* R) : GL n S →* GL n R := Units.map (extHom ι)

theorem extM_cT (ι : S →ₙ+* R) (σS : S →+* S) (σR : R →+* R) (hι : ∀ x, ι (σS x) = σR (ι x)) (A : Matrix n n S) :
    cT σR (extM ι A) = extM ι (cT σS A) := by
  have he : σR (ι 1) = ι 1 := by rw [← hι, map_one]
  ext i j
  by_cases h : i = j
  · subst h; simp [cT, extM, hι, he]
  · simp [cT, extM, Matrix.one_apply, h, Ne.symm h, hι]

theorem extGL_mem (ι : S →ₙ+* R) (σS : S →+* S) (σR : R →+* R) (hι : ∀ x, ι (σS x) = σR (ι x))
    (JS : Matrix n n S) (JR : Matrix n n R) (hJ : JS.map ι = ι 1 • JR) (g : GL n S) (hg : g ∈ UJ σS JS) :
    extGL ι g ∈ UJ σR JR := by
  have hg' : cT σS (g : Matrix n n S) * JS * (g : Matrix n n S) = JS := hg
  show cT σR (extM ι (g : Matrix n n S)) * JR * extM ι (g : Matrix n n S) = JR
  rw [extM_cT ι σS σR hι]
  set A := cT σS (g : Matrix n n S)
  set B := (g : Matrix n n S)
  have k1 : A.map ι * JR = (A * JS).map ι := by
    rw [map_mul_nu, hJ, Matrix.mul_smul]
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, idem_mul]
  have k2 : (1 - ι 1) • (JR * B.map ι) = 0 := by rw [← Matrix.mul_smul, compl_smul_map, Matrix.mul_zero]
  have k3 : (1 - ι 1) • (A.map ι * JR) = 0 := by rw [k1, compl_smul_map]
  have hc : (1 - ι 1) * (1 - ι 1) = 1 - ι 1 := by
    have h := idem_mul ι 1
    linear_combination h
  calc extM ι A * JR * extM ι B
      = (1 - ι 1) • JR + A.map ι * JR * B.map ι := by
        simp only [extM, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
          smul_smul, hc, k2, k3, add_zero, zero_add]
    _ = (1 - ι 1) • JR + ι 1 • JR := by rw [k1, ← map_mul_nu, hg', hJ]
    _ = JR := by rw [← add_smul, sub_add_cancel, one_smul]

theorem smul_map_of (ι : S →ₙ+* R) (c : R) (hc : ∀ x, c * ι x = ι x) (A : Matrix n n S) : c • A.map ι = A.map ι := by
  ext i j; simp [hc]

theorem extM_comm (ι : S →ₙ+* R) (ι' : S' →ₙ+* R) (h0 : ∀ x y, ι x * ι' y = 0) (A : Matrix n n S)
    (B : Matrix n n S') : extM ι A * extM ι' B = extM ι' B * extM ι A := by
  have h1 : ∀ y, (1 - ι 1) * ι' y = ι' y := fun y => by rw [sub_mul, one_mul, h0, sub_zero]
  have h2 : ∀ x, (1 - ι' 1) * ι x = ι x := fun x => by rw [sub_mul, one_mul, mul_comm, h0, sub_zero]
  have hAB : A.map ι * B.map ι' = 0 := by ext i j; simp [Matrix.mul_apply, h0]
  have hBA : B.map ι' * A.map ι = 0 := by ext i j; simp [Matrix.mul_apply, mul_comm, h0]
  simp only [extM, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    smul_map_of ι' _ h1, smul_map_of ι _ h2, hAB, hBA, add_zero, mul_comm (1 - ι 1)]
  abel

end Ext

section Place

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def inrL : Af F →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F)

theorem inrL_mul (a c : Af F) : inrL (a * c) = inrL a * inrL c := Prod.ext (mul_zero (0 : Ainf F)).symm rfl

def inrT : Af F ⊗[F] E →ₙ+* AF F ⊗[F] E where
  toFun := LinearMap.rTensor E inrL
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [add_mul, map_add (f := _), hx, hx']
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [mul_add, map_add (f := _), hy, hy']
      | tmul c d =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, inrL_mul]

def jv (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] v.adicCompletion F →ₙ+* AF F ⊗[F] E :=
  (inrT (E := E)).comp ((Algebra.TensorProduct.comm F E (Af F)).toRingEquiv.toRingHom.toNonUnitalRingHom.comp
    (Formalism.UG.P.afsplitIE (E := E) v))

theorem jv_tmul (v : HeightOneSpectrum (𝓞 F)) (a : E) (b : v.adicCompletion F) :
    jv v (a ⊗ₜ[F] b) = inrL (Formalism.UG.P.afsplitI v b) ⊗ₜ[F] a := rfl

theorem jv_sig (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    jv v (Formalism.UG.sigR σ (v.adicCompletion F) x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (jv v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add (f := _), hx, hx']
  | tmul a b => rfl

theorem jv_inclE (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    jv v (Formalism.UG.inclE (F := F) (v.adicCompletion F) e) = jv v 1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e := by
  show jv v (e ⊗ₜ[F] 1) = jv v (1 ⊗ₜ[F] 1) * ((1 : AF F) ⊗ₜ[F] e)
  rw [jv_tmul, jv_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem jv_fst (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (jv v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', add_zero]
  | tmul a b =>
    rw [jv_tmul, Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _

def backT : AF F ⊗[F] E →+* E ⊗[F] Af F :=
  (Algebra.TensorProduct.comm F (Af F) E).toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

theorem backT_jv (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    backT (jv v x) = Formalism.UG.P.afsplitIE v x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add (f := _), hx, hx']
  | tmul a b => rfl

theorem prV_backT_jv (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    Formalism.UG.prV (E := E) v (backT (jv v x)) = x := by
  rw [backT_jv, Formalism.UG.P.afsplit_prV_IE]

theorem prV_backT_jv_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : E ⊗[F] v.adicCompletion F) :
    Formalism.UG.prV (E := E) w (backT (jv v x)) = 0 := by
  rw [backT_jv, Formalism.UG.P.afsplit_prV_IE_ne v w h]

theorem IE_orth {v v' : HeightOneSpectrum (𝓞 F)} (h : v ≠ v') (x : E ⊗[F] v.adicCompletion F)
    (y : E ⊗[F] v'.adicCompletion F) : Formalism.UG.P.afsplitIE v x * Formalism.UG.P.afsplitIE v' y = 0 := by
  refine Formalism.UG.P.afsplit_inj _ fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [Formalism.UG.P.afsplit_prV_IE_ne _ _ h, mul_zero]
  · rw [Formalism.UG.P.afsplit_prV_IE_ne _ _ hw, zero_mul]

theorem jv_orth {v v' : HeightOneSpectrum (𝓞 F)} (h : v ≠ v') (x : E ⊗[F] v.adicCompletion F)
    (y : E ⊗[F] v'.adicCompletion F) : jv v x * jv v' y = 0 := by
  have k : jv v x * jv v' y = inrT ((Algebra.TensorProduct.comm F E (Af F))
      (Formalism.UG.P.afsplitIE v x * Formalism.UG.P.afsplitIE v' y)) := by
    rw [map_mul, map_mul]; rfl
  rw [k, IE_orth h, map_zero, map_zero]

end Place

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

structure SplitAt (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) where
  sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F
  sig : ∀ x, sp (Formalism.UG.sigR σ (v.adicCompletion F) x) = swapR _ (sp x)
  alg : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)

variable {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

def J1 (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  J.map ((RingHom.fst _ _).comp (s.sp.toRingHom.comp
    (Formalism.UG.inclE (F := F) (v.adicCompletion F))))

theorem J_split (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J i j) = J j i) :
    J.map (s.sp.toRingHom.comp (Formalism.UG.inclE (F := F) (v.adicCompletion F))) =
      splitJ (J1 s J) := by
  refine Matrix.ext fun i j => Prod.ext rfl ?_
  show (s.sp (Formalism.UG.inclE (F := F) _ (J i j))).2 = (s.sp (Formalism.UG.inclE (F := F) _ (J j i))).1
  have h := congrArg Prod.fst (s.sig (Formalism.UG.inclE (F := F) _ (J i j)))
  rw [← hJ i j]
  exact h.symm

theorem split_matrix_det_unit (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) (h : J.det ≠ 0) : IsUnit (J1 s J).det := by
  have := RingHom.map_det ((RingHom.fst _ _).comp (s.sp.toRingHom.comp
    (Formalism.UG.inclE (F := F) (v.adicCompletion F)))) J
  rw [RingHom.mapMatrix_apply] at this
  rw [J1, ← this]
  exact (isUnit_iff_ne_zero.2 h).map _

def e1 (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) (h : J.det ≠ 0) :
    UJ (swapR (v.adicCompletion F)) (splitJ (J1 s J)) ≃* GL (Fin n) (v.adicCompletion F) :=
  Classical.choose (Formalism.UG.Final.SplitIso (v.adicCompletion F) (Fin n) (J1 s J) (split_matrix_det_unit s J h))

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) (h : J.det ≠ 0) (g) :
    e1 s J h g = bc (RingHom.fst _ _) (g : GL (Fin n) (v.adicCompletion F × v.adicCompletion F)) :=
  Classical.choose_spec (Formalism.UG.Final.SplitIso (v.adicCompletion F) (Fin n) (J1 s J) (split_matrix_det_unit s J h)) g

def locH (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) (h : J.det ≠ 0) :
    GL (Fin n) (v.adicCompletion F) →* GL (Fin n) (E ⊗[F] v.adicCompletion F) :=
  (bc s.sp.symm.toRingHom).comp
    ((UJ (swapR (v.adicCompletion F)) (splitJ (J1 s J))).subtype.comp (e1 s J h).symm.toMonoidHom)

theorem locH_fst (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) (h : J.det ≠ 0) (a) :
    bc ((RingHom.fst _ _).comp s.sp.toRingHom) (locH s J h a) = a := by
  have k : ∀ y : GL (Fin n) (v.adicCompletion F × v.adicCompletion F),
      bc ((RingHom.fst _ _).comp s.sp.toRingHom)
        (bc s.sp.symm.toRingHom y) =
      bc (RingHom.fst _ _) y := by
    intro y; apply Units.ext; ext i j; simp [bc]
  rw [locH, MonoidHom.comp_apply, k]
  exact (orderedCechToCatCochainsOne_apply_valueAtSubset s J h ((e1 s J h).symm a)).symm.trans ((e1 s J h).apply_symm_apply a)

theorem locH_mem (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J i j) = J j i)
    (h : J.det ≠ 0) (a) : locH s J h a ∈ Formalism.UG.UPts σ J (v.adicCompletion F) := by
  have hc : s.sp.toRingHom.comp (Formalism.UG.sigR σ (v.adicCompletion F)) =
      (swapR (v.adicCompletion F)).comp s.sp := RingHom.ext s.sig
  have k : (⇑s.sp.symm.toRingHom ∘
      ⇑(s.sp.toRingHom.comp (Formalism.UG.inclE (F := F) (v.adicCompletion F)))) =
      ⇑(Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F)) := by
    funext x; simp
  have key : ∀ x ∈ UJ (swapR (v.adicCompletion F)) (splitJ (J1 s J)),
      bc s.sp.symm.toRingHom x ∈ Formalism.UG.UPts σ J (v.adicCompletion F) := by
    intro x hx
    have h1 := Formalism.UG.P.transport_bc_mem (swapR (v.adicCompletion F)) (Formalism.UG.sigR σ (v.adicCompletion F))
      s.sp.symm.toRingHom (Formalism.UG.P.transport_symm_comp _ _ s.sp hc) (splitJ (J1 s J)) x hx
    rw [← J_split s J hJ, Matrix.map_map, k] at h1
    exact h1
  exact key _ ((e1 s J h).symm a).2

end Local

section Emb

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_herm' (V : HSp D) (i j : Fin V.rank) : D.sp.cm.sig (V.gram i j) = V.gram j i :=
  V.herm.eq (V.frame i) (V.frame j)

abbrev SplitD (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) := SplitAt D.sp.cm.sig v

variable {v : HeightOneSpectrum (𝓞 D.host.F)}

abbrev locV (V : HSp D) (s : SplitD D v) := locH s V.gram (Formalism.L2.Theta.gram_det_ne V)

theorem jv_J (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (V.gram.map (Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F))).map (jv (E := D.host.E) v) =
      jv (E := D.host.E) v 1 • Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF D.host.F) V.gram := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR]
  exact jv_inclE v _

theorem embV_mem (V : HSp D) (s : SplitD D v) (a : GL (Fin V.rank) (v.adicCompletion D.host.F)) :
    extGL (jv v) (locV V s a) ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
  extGL_mem (jv v) (Formalism.UG.sigR D.sp.cm.sig _) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (jv_sig _ v) _ _
    (jv_J V v) _ (locH_mem s V.gram (gram_herm' V) _ a)

def embV (V : HSp D) (s : SplitD D v) : GL (Fin V.rank) (v.adicCompletion D.host.F) →* GA D V :=
  MonoidHom.codRestrict ((extGL (jv v)).comp (locV V s)) (HR (AF D.host.F) D.sp.cm.sig V.gram) (embV_mem V s)

theorem embV_coe (V : HSp D) (s : SplitD D v) (a : GL (Fin V.rank) (v.adicCompletion D.host.F)) :
    (matHom V (embV V s a)).val = extM (jv v) (locV V s a).val := rfl

theorem infHom_entry (V : HSp D) (g : GA D V) (i j : Fin V.rank) :
    (infHom V g).val i j = Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _) ((matHom V g).val i j) := rfl

theorem embV_fin (V : HSp D) (s : SplitD D v) (a : GL (Fin V.rank) (v.adicCompletion D.host.F)) :
    embV V s a ∈ GfC V := by
  rw [GfC, MonoidHom.mem_ker]
  apply Units.ext
  ext i j
  rw [infHom_entry, embV_coe, Units.val_one]
  by_cases h : i = j
  · subst h; simp [extM, jv_fst]
  · simp [extM, jv_fst, h]

theorem compV_entry (V : HSp D) (w : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) (i j : Fin V.rank) :
    (compV V w g).val i j = Formalism.UG.prV w (backT ((matHom V g).val i j)) := rfl

theorem compV_embV (V : HSp D) (s : SplitD D v) (a : GL (Fin V.rank) (v.adicCompletion D.host.F)) :
    compV V v (embV V s a) = locV V s a := by
  apply Units.ext
  ext i j
  rw [compV_entry, embV_coe]
  by_cases h : i = j
  · subst h; simp [extM, prV_backT_jv]
  · simp [extM, prV_backT_jv, h]

theorem compV_embV_ne (V : HSp D) (s : SplitD D v) (a : GL (Fin V.rank) (v.adicCompletion D.host.F))
    (w : HeightOneSpectrum (𝓞 D.host.F)) (hw : w ≠ v) : compV V w (embV V s a) = 1 := by
  apply Units.ext
  ext i j
  rw [compV_entry, embV_coe, Units.val_one]
  by_cases h : i = j
  · subst h; simp [extM, prV_backT_jv_ne v w hw]
  · simp [extM, prV_backT_jv_ne v w hw, h]

theorem embV_at (V : HSp D) (s : SplitD D v) (a : GL (Fin V.rank) (v.adicCompletion D.host.F)) :
    Formalism.UG.bc ((RingHom.fst _ _).comp s.sp.toRingHom) (compV V v (embV V s a)) = a := by
  rw [compV_embV]; exact locH_fst s _ _ a

theorem embV_inj (V : HSp D) (s : SplitD D v) : Function.Injective (embV V s) := by
  intro a b hab
  rw [← embV_at V s a, ← embV_at V s b, hab]

theorem embV_comm (V : HSp D) {v v' : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ v') (s : SplitD D v)
    (s' : SplitD D v') (a : GL (Fin V.rank) (v.adicCompletion D.host.F))
    (b : GL (Fin V.rank) (v'.adicCompletion D.host.F)) : embV V s a * embV V s' b = embV V s' b * embV V s a := by
  apply Subtype.ext
  apply Units.ext
  exact extM_comm (jv v) (jv v') (jv_orth h) _ _


open Classical in
def embOn (V : HSp D) (T : Set (HeightOneSpectrum (𝓞 D.host.F))) (s : ∀ v ∈ T, SplitD D v)
    (v : HeightOneSpectrum (𝓞 D.host.F)) : GL (Fin V.rank) (v.adicCompletion D.host.F) →* GA D V :=
  if hv : v ∈ T then embV V (s v hv) else 1

theorem embOn_mem (V : HSp D) {T : Set (HeightOneSpectrum (𝓞 D.host.F))} (s : ∀ v ∈ T, SplitD D v)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ T) : embOn V T s v = embV V (s v hv) := dif_pos hv

theorem embOn_not (V : HSp D) {T : Set (HeightOneSpectrum (𝓞 D.host.F))} (s : ∀ v ∈ T, SplitD D v)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ T) (a : GL (Fin V.rank) (v.adicCompletion D.host.F)) :
    embOn V T s v a = 1 := by
  rw [embOn, dite_eq_right hv, MonoidHom.one_apply]

def splitEmbOn (V : HSp D) (K : Set (GA D V)) (T : Set (HeightOneSpectrum (𝓞 D.host.F)))
    (s : ∀ v ∈ T, SplitD D v) (hK : ∀ v (hv : v ∈ T), ∀ a ∈ Kv v V.rank, embV V (s v hv) a ∈ K)
    (h1 : (1 : GA D V) ∈ K) : SplitEmb V K where
  Sp := T
  sp v hv := (s v hv).sp
  sp_sig v hv := (s v hv).sig
  sp_alg v hv := (s v hv).alg
  emb := embOn V T s
  emb_fin v a := by
    by_cases hv : v ∈ T
    · rw [embOn_mem V s hv]; exact embV_fin V (s v hv) a
    · rw [embOn_not V s hv]; exact (GfC V).one_mem
  emb_at v hv a := by rw [embOn_mem V s hv]; exact embV_at V (s v hv) a
  emb_off v hv a w hw := by rw [embOn_mem V s hv]; exact compV_embV_ne V (s v hv) a w hw
  emb_K v a ha := by
    by_cases hv : v ∈ T
    · rw [embOn_mem V s hv]; exact hK v hv a ha
    · rw [embOn_not V s hv]; exact h1
  emb_comm v v' h a b := by
    by_cases hv : v ∈ T <;> by_cases hv' : v' ∈ T
    · rw [embOn_mem V s hv, embOn_mem V s hv']; exact embV_comm V h (s v hv) (s v' hv') a b
    · rw [embOn_not V s hv' b, mul_one, one_mul]
    · rw [embOn_not V s hv a, mul_one, one_mul]
    · rw [embOn_not V s hv a, embOn_not V s hv' b]

end Emb

section Level

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000 in
theorem one_mem_KpC (V : HSp D) (N : ℕ) : (1 : GA D V) ∈ Formalism.L2.NTheta.KpC V N := by
  have hf : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 := by
    show ((1 : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E))).map _ = 1
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨(GfC V).one_mem, fun y => by rw [hf, Matrix.one_mulVec], fun v hv => absurd hv (Finset.notMem_empty v)⟩,
    fun y _ => ⟨0, zero_mem _, by rw [hf, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩


end Level

section Clauses

variable {G : Type} [Group G]

end Clauses

section Checks

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Checks

end Formalism.IndefR.NX
