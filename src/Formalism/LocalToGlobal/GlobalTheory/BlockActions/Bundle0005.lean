module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle0004
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle0003
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FormsOfLatticeExtension
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.InJSymRestrict

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassInjectiveOfSelfDual
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions NumberField

theorem T_sub_one_ge (D : D7) (u : D.what₂.Word) :
    D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 ≤ (D.mem u).A.T - 1 := by
  set M : ℕ := D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 with hM
  obtain ⟨π, -, hπ, hπ1⟩ := D.T_norm u
  obtain ⟨α, hα⟩ := Ideal.mem_span_singleton'.mp hπ1
  set cj : D.host.E →+* D.host.E := (D.host.conj : D.host.E →+* D.host.E) with hcj
  let αb : 𝓞 D.host.E := ⟨cj (α : D.host.E), (α.2).map cj.toIntAlgHom⟩
  let b : 𝓞 D.host.E := α + αb + (M : 𝓞 D.host.E) * α * αb
  have hαE : (π : D.host.E) = 1 + (M : D.host.E) * (α : D.host.E) := by
    have := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hα
    simp only [map_mul, map_sub, map_one, map_natCast, RingOfIntegers.coe_eq_algebraMap] at this ⊢
    rw [← hM] at this
    linear_combination -this
  have hcπ : cj (π : D.host.E) = 1 + (M : D.host.E) * cj (α : D.host.E) := by
    rw [hαE, map_add (f := _), map_mul, map_one, map_natCast]
  have hT : ((D.mem u).A.T : D.host.E) - 1 = (M : D.host.E) * (b : D.host.E) := by
    have hπ' : (π : D.host.E) * cj (π : D.host.E) = ((D.mem u).A.T : D.host.E) := hπ
    rw [← hπ', hcπ, hαE]
    simp only [b, αb, map_add (f := _), map_mul, map_natCast, RingOfIntegers.coe_eq_algebraMap]
    show _ = (M : D.host.E) * ((α : D.host.E) + cj (α : D.host.E) + (M : D.host.E) * (α : D.host.E) * cj (α : D.host.E))
    ring
  have hMpos : 0 < M := by
    have hq : 0 < D.host.q := by have := D.host.qd_big.1; omega
    have hd : 0 < D.host.d := by have := D.host.qd_big.2; omega
    have hg0 := (D.host.g_prime 0).pos
    have hg1 := (D.host.g_prime 1).pos
    have hn : 0 < D.host.QS := D.host.QS_pos
    rw [hM]; positivity
  have hME : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
  set r : ℚ := (((D.mem u).A.T : ℚ) - 1) / (M : ℚ) with hr
  have hbr : (b : D.host.E) = algebraMap ℚ D.host.E r := by
    rw [hr, map_div₀, map_sub, map_natCast, map_one, map_natCast, hT]
    field_simp
  have hint : IsIntegral ℤ r := by
    have h1 : IsIntegral ℤ (algebraMap ℚ D.host.E r) := hbr ▸ RingOfIntegers.isIntegral_coe b
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ D.host.E) (algebraMap ℚ D.host.E).injective).mp h1
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hTq : ((D.mem u).A.T : ℚ) - 1 = (M : ℚ) * (z : ℚ) := by
    have : (z : ℚ) = r := hz
    rw [this, hr]; field_simp
  have hT2 := (D.mem u).A.T_prime.two_le
  have hTz : ((D.mem u).A.T : ℤ) - 1 = (M : ℤ) * z := by exact_mod_cast hTq
  have hz1 : 1 ≤ z := by
    by_contra hc
    push Not at hc
    have : (M : ℤ) * z ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    omega
  have : (M : ℤ) ≤ ((D.mem u).A.T : ℤ) - 1 := by nlinarith
  omega

theorem finrank_host_lt_T_sub_one (D : D7) (u : D.what₂.Word) : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1 := by
  have hf : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h := T_sub_one_ge D u
  have hq : 2 ≤ D.host.q := by have := D.host.qd_big.1; omega
  have hd : 2 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hg0 := (D.host.g_prime 0).two_le
  have hg1 := (D.host.g_prime 1).two_le
  have hgg : 4 ≤ D.host.g 0 * D.host.g 1 := by nlinarith
  have hgg2 : 16 ≤ (D.host.g 0 * D.host.g 1) ^ 2 := by nlinarith
  have hQ : 0 < D.host.QS := D.host.QS_pos
  have hN : 0 < D.host.QS * D.host.q * D.host.d := by positivity
  haveI : NeZero (D.host.QS * D.host.q * D.host.d) := ⟨hN.ne'⟩
  have hcard : Nat.card D.R.GG ≤ Nat.card (ZMod (D.host.QS * D.host.q * D.host.d))ˣ :=
    Nat.card_le_card_of_surjective _ D.host.der.art_surj
  have hGG : Nat.card D.R.GG = 4 * D.R.ord := D.R.natCard_GG
  have hphi : Nat.card (ZMod (D.host.QS * D.host.q * D.host.d))ˣ ≤ D.host.QS * D.host.q * D.host.d := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact Nat.totient_le _
  have key : D.host.QS * D.host.q * D.host.d < D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 := by
    nlinarith
  omega

theorem class_injective_of_self_dual
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : Formalism.L2.Forms.FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramP D) (Tf.clsP.lat c) =
        (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E))) :
    ClassMapInjective :=
  classMapInjective_of_finrank_lt hSD (fun D u _ _ _ => finrank_host_lt_T_sub_one D u)

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfClasses
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix
open scoped ComplexOrder

variable {D : D7}

theorem sig_at (ι : D.host.E →+* ℂ) (x : D.host.E) : ι (sigD D x) = starRingEnd ℂ (ι x) :=
  D.sp.cm.cmUnram.2.1 ι x

theorem map_cT_at {m n : Type} (ι : D.host.E →+* ℂ) (M : Matrix m n D.host.E) :
    ((M.map (sigD D : D.host.E →+* D.host.E))ᵀ).map ι = (M.map ι)ᴴ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RingHom.coe_coe]
  rw [sig_at]
  rfl

theorem gramN_posDef_at {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf)
    (ι : D.host.E →+* ℂ) : ((gramN D D.R.m le_rfl).map ι).PosDef := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  have hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl := hC
  set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := C.1.map ι with hA
  have hG : (gramN D D.R.m le_rfl).map ι = Aᴴ * A := by
    rw [← hC', Matrix.map_mul, map_cT_at, hA]
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    have h1 : (C.1⁻¹ * C.1).map ι = 1 := by
      rw [Matrix.nonsing_inv_mul _ hCi, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun v => ((C.1⁻¹).map ι) *ᵥ v) hxy
    simp only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2
    exact h2
  rw [hG]
  exact Matrix.PosDef.conjTranspose_mul_self A hinj

theorem gramP_posDef_at {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf)
    (ι : D.host.E →+* ℂ) : ((gramP D).map ι).PosDef := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  have hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl := hC
  obtain ⟨L, hL⟩ := iXm_leftInv D
  set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) ℂ := (C.1 * iXm D).map ι with hA
  have hG : (gramP D).map ι = Aᴴ * A := by
    have e1 : ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (((C.1).map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) * iXm D =
        ((C.1 * iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (C.1 * iXm D) := by
      rw [Matrix.map_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [gramP_eq, ← hC', e1, Matrix.map_mul, map_cT_at, hA]
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    have h1 : ((L * C.1⁻¹) * (C.1 * iXm D)).map ι = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc C.1⁻¹, Matrix.nonsing_inv_mul _ hCi, Matrix.one_mul, hL,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun v => ((L * C.1⁻¹).map ι) *ᵥ v) hxy
    simp only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2
    exact h2
  rw [hG]
  exact Matrix.PosDef.conjTranspose_mul_self A hinj

theorem framesAt : FramesAt := by
  intro D u Ch chOf Tf s
  constructor
  · have h := fun τ => exists_on_of_posDef (gramC (gramN D D.R.m le_rfl) (embS D s) τ) (gramN_posDef_at Tf (embS D s τ))
    choose o ho1 ho2 using h
    exact ⟨⟨o, ho1⟩, fun τ => Or.inl (ho2 τ)⟩
  · have h := fun τ => exists_on_of_posDef (gramC (gramP D) (embS D s) τ) (gramP_posDef_at Tf (embS D s τ))
    choose o ho1 ho2 using h
    exact ⟨⟨o, ho1⟩, fun τ => Or.inl (ho2 τ)⟩

theorem norm_bound_of_classes (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) (hC : NormClsAt) : NormBoundAtInfinity :=
  norm_bound_of_classes_frames h1 h2 framesAt hC

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.StabFunGen
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section GenE

theorem ext_mem_gen {A S : Type} [CommRing A] [Ring S] {n N : ℕ} [Module S (Fin N → A)] [Module S (Fin n → A)]
    (Λm Λd : Submodule S (Fin N → A)) (Λp : Submodule S (Fin n → A)) (hmd : Λm ≤ Λd)
    (I : Matrix (Fin N) (Fin n) A) (P : Matrix (Fin n) (Fin N) A) (k : Matrix (Fin n) (Fin n) A)
    (G : Matrix (Fin N) (Fin N) A) (hPI : P * I = 1) (hG : G = I * k * P + (1 - I * P))
    (hk : ∀ x, x ∈ Λp ↔ k *ᵥ x ∈ Λp) (hI : ∀ x ∈ Λp, I *ᵥ x ∈ Λm) (hO : ∀ x ∈ Λd, P *ᵥ x ∈ Λp)
    (x : Fin N → A) : (x ∈ Λd ↔ G *ᵥ x ∈ Λd) ∧ (x ∈ Λd → G *ᵥ x - x ∈ Λm) := by
  have hGx : G *ᵥ x - x = I *ᵥ (k *ᵥ (P *ᵥ x)) - I *ᵥ (P *ᵥ x) := by
    simp only [hG, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    abel
  have hPIv : ∀ y, P *ᵥ (I *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hPI, Matrix.one_mulVec]
  have e : G *ᵥ x = x + (I *ᵥ (k *ᵥ (P *ᵥ x)) - I *ᵥ (P *ᵥ x)) := by rw [← hGx]; abel
  have hPG : P *ᵥ (G *ᵥ x) = k *ᵥ (P *ᵥ x) := by
    rw [e, Matrix.mulVec_add, Matrix.mulVec_sub, hPIv, hPIv]; abel
  have hdiff : P *ᵥ x ∈ Λp → G *ᵥ x - x ∈ Λm := fun h => by
    rw [hGx]; exact sub_mem (hI _ ((hk _).1 h)) (hI _ h)
  refine ⟨⟨fun hx => ?_, fun hx => ?_⟩, fun hx => hdiff (hO x hx)⟩
  · have e2 : G *ᵥ x = x + (G *ᵥ x - x) := by abel
    rw [e2]; exact add_mem hx (hmd (hdiff (hO x hx)))
  · have h1 : P *ᵥ x ∈ Λp := (hk _).2 (by rw [← hPG]; exact hO _ hx)
    have e2 : x = G *ᵥ x - (G *ᵥ x - x) := by abel
    rw [e2]; exact sub_mem hx (hmd (hdiff h1))

theorem stabFun_gen {A R M : Type} [CommRing A] [CommRing R] [Algebra R A] [AddCommGroup M] [Module R M] {N : ℕ}
    (Λ Λm : Submodule R (Fin N → A)) (f : Λ →ₗ[R] M) (g : GL (Fin N) A)
    (hst : ∀ x, x ∈ Λ ↔ (g : Matrix (Fin N) (Fin N) A) *ᵥ x ∈ Λ)
    (hd : ∀ x ∈ Λ, (g : Matrix (Fin N) (Fin N) A) *ᵥ x - x ∈ Λm) (hm : Λm ≤ Λ)
    (hf : ∀ y : Λ, y.1 ∈ Λm → f y = 0) : g ∈ stabFun Λ f := by
  refine ⟨hst, fun x => ?_⟩
  have e : (⟨(g : Matrix (Fin N) (Fin N) A) *ᵥ (x : Fin N → A), (hst x).1 x.2⟩ : Λ) = x + ⟨_, hm (hd x.1 x.2)⟩ :=
    Subtype.ext (by simp)
  rw [e, map_add (f := _), hf ⟨_, hm (hd x.1 x.2)⟩ (hd x.1 x.2), add_zero]

end GenE

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem proj_dual (Tf : FormsTiedSym D u Ch chOf) (P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E)
    (hP1 : P * iXm D = 1) (hPz : P *ᵥ Tf.til.z0 = 0) :
    ∀ y ∈ Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
      (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb), P *ᵥ y ∈ Tf.clsP.lev.Lb := by
  have hiX : ∀ x, iXm D *ᵥ x = iXc D x := fun x => by simp only [iXm, LinearMap.toMatrix'_mulVec]
  obtain ⟨a0, ha0⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have ha : a0 ≠ 0 := by
    rintro rfl
    have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
    have h := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha0, zero_smul] at h
    simp [Formalism.UG.hform] at h
    exact hT h.symm
  have hPzc : P *ᵥ zc D = 0 := by
    rw [ha0, Matrix.mulVec_smul] at hPz
    exact (smul_eq_zero.mp hPz).resolve_left ha
  have hin := (lat_in_out Tf P hP1 hPz).1
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, s, rfl⟩ := span_iXc_zc D y
    have e : P *ᵥ (iXc D x + s • zc D) = x := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hPzc, smul_zero, add_zero, ← hiX, Matrix.mulVec_mulVec, hP1,
        Matrix.one_mulVec]
    rw [e]
    have hd : x ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) Tf.clsP.lev.Lb := by
      intro x' hx'
      have h := hy (iXc D x') (by rw [← hiX]; exact hin x' hx')
      rwa [hform_add_right, hform_smul_rightB, hform_iXc, hform_iXc_zc, mul_zero, add_zero] at h
    have := Tf.clsP.lev.Lb_dual x hd
    simpa using this
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul D.host.E a x, Matrix.mulVec_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem extV_lat (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E)
    (hP1 : P * iXm D = 1) (hPz : P *ᵥ Tf.til.z0 = 0)
    (Λd : Submodule (intV D.host.E v) (Fin (D.R.N D.R.m) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))
    (hmd : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb ≤ Λd)
    (hO : ∀ x ∈ Λd, (P.map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ x ∈
      latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) Tf.clsP.lev.Lb)
    (x : Fin (D.R.N D.R.m) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    (x ∈ Λd ↔ G.1.map (prV (E := D.host.E) v) *ᵥ x ∈ Λd) ∧
      (x ∈ Λd → G.1.map (prV (E := D.host.E) v) *ᵥ x - x ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb) := by
  have hκv : bc (prV (E := D.host.E) v) κ.1 ∈ Tf.clsP.lev.Uloc v := ((Tf.clsP.lev.U_eq κ.1).1 κ.2).2 v
  have hκst := (Subgroup.mem_inf.mp (Tf.clsP.lev.Uloc_lev v hκv)).2
  have hin := (lat_in_out Tf P hP1 hPz).1
  have hI := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (iXm D) _ _ hin
  have hform := ext_form Tf (inclE (F := D.host.F) (v.adicCompletion D.host.F)) P hP1 hPz _ _ (isExt_prV v hE)
  rw [Matrix.map_mul] at hform
  have hPI : (P.map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *
      ((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) = 1 := by
    rw [← Matrix.map_mul, hP1, Matrix.map_one _ (map_zero _) (map_one _)]
  exact ext_mem_gen _ Λd _ hmd _ _ (κ.1.1.map (prV (E := D.host.E) v)) _ hPI hform (fun y => hκst y) hI hO x


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem extV_unit (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    bc (prV (E := D.host.E) v) G ∈ UJ (sigR (sigD D) (v.adicCompletion D.host.F))
      ((gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) := by
  have hκv : bc (prV (E := D.host.E) v) κ.1 ∈ Tf.clsP.lev.Uloc v := ((Tf.clsP.lev.U_eq κ.1).1 κ.2).2 v
  have hκU0 := Tf.clsP.lev.Uloc_le v hκv
  have hκU : cT (sigR (sigD D) (v.adicCompletion D.host.F)) (κ.1.1.map (prV (E := D.host.E) v)) *
      (gramP D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) * κ.1.1.map (prV (E := D.host.E) v) =
      (gramP D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) := hκU0
  show cT (sigR (sigD D) (v.adicCompletion D.host.F)) (G.1.map (prV (E := D.host.E) v)) *
      (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) * G.1.map (prV (E := D.host.E) v) =
      (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))
  exact extUR Tf _ hκU _ (isExt_prV v hE)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem extV_stabL (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    bc (prV (E := D.host.E) v) G ∈ stabGL (latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
      (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb) := by
  obtain ⟨P, hP1, hPz⟩ := exists_projP Tf
  have hout := (lat_in_out Tf P hP1 hPz).2
  have hO := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) P _ _ hout
  intro x
  exact (extV_lat Tf κ G hE v P hP1 hPz _ le_rfl hO x).1


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem extV_level (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    bc (prV (E := D.host.E) v) G ∈ levelVL (sigD D) (gramN D D.R.m le_rfl) v (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb :=
  Subgroup.mem_inf.mpr ⟨extV_unit Tf κ G hE v, extV_stabL Tf κ G hE v⟩


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem extV_fT (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hT : ((D.mem u).A.T : 𝓞 D.host.F) ∈ v.asIdeal) :
    bc (prV (E := D.host.E) v) G ∈ stabFun _ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.fT v hT) := by
  obtain ⟨P, hP1, hPz⟩ := exists_projP Tf
  have hOd := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) P _ _ (proj_dual Tf P hP1 hPz)
  have hmd : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb ≤
      latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
          (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb)) :=
    Submodule.span_mono (Set.image_mono fun y hy =>
      Submodule.subset_span ((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb_int y hy))
  exact stabFun_gen _ _ _ (bc (prV (E := D.host.E) v) G)
    (fun x => (extV_lat Tf κ G hE v P hP1 hPz _ hmd hOd x).1)
    (fun x hx => (extV_lat Tf κ G hE v P hP1 hPz _ hmd hOd x).2 hx) hmd
    (fun y hy => (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.fT_L v hT y hy)

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.StabRestrict
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

set_option maxHeartbeats 4000000 in
theorem stab_restrict (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl))
    (hγ : γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range)
    (δ : UJ (sigD D : D.host.E →+* D.host.E) (gramP D))
    (hδ : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ.1.1 ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1)) :
    δ ∈ (Tf.clsP.stabI c).range := by
  set Km := Tf.cls D.R.m le_rfl (Or.inr rfl) with hKm
  rw [Km.stabI_range] at hγ
  obtain ⟨κ, hκ, hκe⟩ := Subgroup.mem_map.mp hγ
  rw [Tf.clsP.stabI_range]
  have hdet : IsUnit ((Tf.clsP.y c).1.1).det := (Matrix.isUnit_iff_isUnit_det _).mp (Tf.clsP.y c).1.isUnit
  obtain ⟨g, hg, hu⟩ := til_ext Tf (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.clsP.y c).1.1
  set Gc : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := ((Matrix.isUnit_iff_isUnit_det g).mpr (hu hdet)).unit with hGcdef
  have hGcv : Gc.1 = g := IsUnit.unit_spec _
  have hGc : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.clsP.y c).1.1 Gc.1 := by rw [hGcv]; exact hg
  have e1 := Tf.tilAd.til_ad c Gc hGc
  have hGc1 : Gc = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.til.ga c).1 * (Km.y ((D.fm u).til c)).1 *
      ((Tf.tilAd.ka c).1)⁻¹ := eq_mul_inv_of_mul_eq e1.symm
  have hbc : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 = (Km.y ((D.fm u).til c)).1 * κ * ((Km.y ((D.fm u).til c)).1)⁻¹ := by
    rw [← hκe]; rfl
  set Γ : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((Tf.til.ga c).1 * γ.1 * ((Tf.til.ga c)⁻¹).1) with hΓ
  have hGK : Gc⁻¹ * Γ * Gc ∈ Km.lev.U := by
    have e : Gc⁻¹ * Γ * Gc = (Tf.tilAd.ka c).1 * κ * ((Tf.tilAd.ka c).1)⁻¹ := by
      rw [hΓ, map_mul, map_mul, hbc, hGc1]
      have hi : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((Tf.til.ga c)⁻¹).1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.til.ga c).1)⁻¹ := by
        rw [← map_inv]; rfl
      rw [hi]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Tf.tilAd.ka c).2 hκ) (Subgroup.inv_mem _ (Tf.tilAd.ka c).2)
  have hinv : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((Tf.clsP.y c).1.1)⁻¹ (Gc⁻¹).1 :=
    isExt_inv hGc (Units.inv_mul Gc) (Matrix.mul_nonsing_inv _ hdet)
  have hΓ1 : (Γ.1 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) =
      ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [hΓ]; rfl
  have hΓE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (δ.1.1.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) Γ.1 := by
    rw [hΓ1]; exact isExt_map hδ
  set K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
    ((Tf.clsP.y c).1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1 * (Tf.clsP.y c).1 with hK
  have hKE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) K.1 (Gc⁻¹ * Γ * Gc).1 := by
    have e : K.1 = ((Tf.clsP.y c).1.1)⁻¹ * δ.1.1.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (Tf.clsP.y c).1.1 := by
      rw [hK, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]; rfl
    rw [e, Units.val_mul, Units.val_mul]
    exact isExt_mul (isExt_mul hinv hΓE) hGc
  have hKU := lev_mem Tf K _ hKE hGK
  refine Subgroup.mem_map.mpr ⟨K, hKU, ?_⟩
  show (Tf.clsP.y c).1 * K * ((Tf.clsP.y c).1)⁻¹ = _
  rw [hK]
  group

end Formalism.L2.GlobalTheoryTheory.Br
end
end

