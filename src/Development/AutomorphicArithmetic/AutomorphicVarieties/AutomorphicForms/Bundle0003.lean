module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep
open scoped TensorProduct

namespace UpperTheory.V.TR

variable {E : Type} [Field E] [NumberField E] {a : ℕ}


variable (E a) in
def regFun : Subalgebra ℂ (GL (Fin a) (Rinf E) → ℂ) :=
  Algebra.adjoin ℂ ({f | ∃ v i j, f = fun y => ((y.val i j v : ℝ) : ℂ)} ∪ {f | ∃ v, f = fun y => ((y.val.det v : ℝ) : ℂ)⁻¹})


variable (E a) in
structure AlgRep where

  d : ℕ

  mat : GL (Fin a) (Rinf E) →* Matrix (Fin d) (Fin d) ℂ
  reg : ∀ i j, (fun y => mat y i j) ∈ regFun E a
  pos : 0 < d
  irred : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ W, mat y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤



open Classical in
def AlgRep.HasInfChar (Ξ : AlgRep E a) (v : InfinitePlace E) (m : Multiset ℂ) : Prop :=
  let dmat (X : Lie E a) : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
    Matrix.of fun i j =>
      fderiv ℝ (fun x : Lie E a => if h : IsUnit (Matrix.of x) then Ξ.mat h.unit i j else 0)
        (oneL E a) X
  Multiset.card m = a ∧ ∀ u : ℂ,
    Formalism.REAL.qdet (fun i j => dmat (toL (Matrix.single i j (Pi.single v 1))))
        (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)



section Complex

omit [NumberField E]

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)

end Complex

variable [IsTotallyReal E]


end UpperTheory.V.TR

namespace UpperTheory.V.Af

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def levelRep (Γ : Subgroup (GL (Fin a) E)) (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ}
    (ξ : GL (Fin a) E →* Matrix (Fin d) (Fin d) ℂ) :
    Representation ℂ ↥Γ ((GL (Fin a) (Af E) ⧸ U) → Fin d → ℂ) where
  toFun γ :=
    { toFun := fun f x => ξ γ *ᵥ f ((GeneralLinearGroup.map (algebraMap E (Af E)) γ.1)⁻¹ • x)
      map_add' := fun f g => funext fun x => by simp [Matrix.mulVec_add]
      map_smul' := fun c f => funext fun x => by simp [Matrix.mulVec_smul] }
  map_one' := by ext f x; simp
  map_mul' γ δ := by ext f x; simp [mul_smul]

def cohDim (Γ : Subgroup (GL (Fin a) E)) (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ}
    (ξ : GL (Fin a) E →* Matrix (Fin d) (Fin d) ℂ) : Cardinal :=
  Cardinal.sum fun q : ℕ => Module.rank ℂ (groupCohomology (Rep.of (levelRep Γ U ξ)) q)

variable [_root_.NumberField.IsTotallyComplex E]

def ratC (Ξ : GlobalTheory.GKCoh.AlgRep E a) : GL (Fin a) E →* Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  Ξ.mat.comp ((GeneralLinearGroup.map (pInf E)).comp (ratGL E a))


omit [_root_.NumberField.IsTotallyComplex E] in
def AlgInfChar (Ξ : GlobalTheory.GKCoh.AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (fun i j => (1 / 2 : ℂ) • (Ξ.dmat (toL (Matrix.single i j (atEmb τ 1))) -
      Complex.I • Ξ.dmat (toL (Matrix.single i j (atEmb τ Complex.I))))) (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

def IsFinComp (π : CuspSub E a) (σ : SmIrr (GL (Fin a) (Af E))) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = π.finPart g (f v)


omit [_root_.NumberField.IsTotallyComplex E] in
def IsConjBy (σ : ℂ ≃+* ℂ) (τ τ' : SmIrr (GL (Fin a) (Af E))) : Prop :=
  ∃ T : τ.V ≃+ τ'.V, (∀ (c : ℂ) v, T (c • v) = σ c • T v) ∧ ∀ g v, T (τ.ρ g v) = τ'.ρ g (T v)

end UpperTheory.V.Af
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.V.Af

variable {F : Type} [Field F] [NumberField F] {n M N : ℕ}

theorem mem_Ohat {x : Af F} : x ∈ Ohat F ↔ x ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := by
  rw [GroundTheory.Global.mem_integralFiniteAdeles, Ohat, Subring.mem_iInf]
  rfl

theorem mem_KLev {g : GL (Fin n) (Af F)} :
    g ∈ KLev F n M ↔ (∀ a b, g a b ∈ Ohat F) ∧ (∀ a b, (g⁻¹ : GL (Fin n) (Af F)) a b ∈ Ohat F) ∧
      ∀ a b, ∃ y ∈ Ohat F, g a b - (1 : Matrix (Fin n) (Fin n) (Af F)) a b = (M : Af F) * y := by
  have h1 : ∀ a b, (((1 : Matrix (Fin n) (Fin n) ↥(Ohat F)) a b : ↥(Ohat F)) : Af F) =
      (1 : Matrix (Fin n) (Fin n) (Af F)) a b := fun a b => by
    simp only [Matrix.one_apply]; split_ifs <;> rfl
  have h2 : ∀ a b, (1 : Matrix (Fin n) (Fin n) (↥(Ohat F) ⧸ Ideal.span {(M : ↥(Ohat F))})) a b =
      Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) ↥(Ohat F)) a b) := fun a b => by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun a b => (k a b).2, fun a b => ?_, fun a b => ?_⟩
    · rw [← map_inv]; exact ((k⁻¹ : GL (Fin n) ↥(Ohat F)) a b).2
    · have e : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat F))}) (k a b) = _ :=
        (congrArg (fun x : GL (Fin n) (↥(Ohat F) ⧸ Ideal.span {(M : ↥(Ohat F))}) => x a b) hk).trans (h2 a b)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 e)
      refine ⟨y, y.2, ?_⟩
      rw [← h1]
      exact congrArg Subtype.val hy
  · rintro ⟨ha, hb, hc⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) (Ohat F).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin n) ↥(Ohat F) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin n) (Af F)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    refine ⟨k, ?_, Units.ext rfl⟩
    refine Units.ext (Matrix.ext fun a b => ?_)
    refine Eq.trans ?_ (h2 a b).symm
    obtain ⟨y, hy, e⟩ := hc a b
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨⟨y, hy⟩, Subtype.ext ?_⟩)
    rw [← h1] at e
    exact e

theorem KLev_le_of_dvd (h : M ∣ N) : KLev F n N ≤ KLev F n M := by
  obtain ⟨c, rfl⟩ := h
  intro g hg
  obtain ⟨ha, hb, hc⟩ := mem_KLev.1 hg
  refine mem_KLev.2 ⟨ha, hb, fun a b => ?_⟩
  obtain ⟨y, hy, e⟩ := hc a b
  exact ⟨c * y, mul_mem (natCast_mem _ c) hy, by rw [e, Nat.cast_mul, mul_assoc]⟩

theorem KLev_le_integral : KLev F n M ≤ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL F n := fun _ hg =>
  (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff F n).2
    ⟨fun a b => mem_Ohat.1 ((mem_KLev.1 hg).1 a b), fun a b => mem_Ohat.1 ((mem_KLev.1 hg).2.1 a b)⟩

theorem isOpen_Ohat : IsOpen (Ohat F : Set (Af F)) := by
  convert GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 F) (K := F) using 1
  exact Set.ext fun _ => mem_Ohat

theorem isOpen_KLev (hM : 1 ≤ M) : IsOpen (KLev F n M : Set (GL (Fin n) (Af F))) := by
  have hM' : (M : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set u : Af F := algebraMap F (Af F) (M : F)⁻¹
  have hu : u * M = 1 := by rw [← map_natCast (algebraMap F (Af F)), ← map_mul, inv_mul_cancel₀ hM', map_one]
  have e : (KLev F n M : Set (GL (Fin n) (Af F))) =
      (⋂ a, ⋂ b, (fun g : GL (Fin n) (Af F) => g a b) ⁻¹' Ohat F) ∩
      ((⋂ a, ⋂ b, (fun g : GL (Fin n) (Af F) => (g⁻¹ : GL (Fin n) (Af F)) a b) ⁻¹' Ohat F) ∩
      ⋂ a, ⋂ b, (fun g : GL (Fin n) (Af F) => u * (g a b - (1 : Matrix (Fin n) (Fin n) (Af F)) a b)) ⁻¹' Ohat F) := by
    ext g
    simp only [SetLike.mem_coe, mem_KLev, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun a b => ⟨?_, fun h => ⟨_, h, ?_⟩⟩
    · rintro ⟨y, hy, e⟩
      rwa [e, ← mul_assoc, hu, one_mul]
    · rw [← mul_assoc, mul_comm _ u, hu, one_mul]
  rw [e]
  have c : ∀ a b, Continuous fun g : GL (Fin n) (Af F) => g a b := fun a b =>
    Continuous.matrix_elem Units.continuous_val a b
  refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_) <;>
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => isOpen_Ohat.preimage ?_
  · exact c a b
  · exact (c a b).comp continuous_inv
  · exact continuous_const.mul ((c a b).sub continuous_const)

theorem isCompact_KLev (hM : 1 ≤ M) : IsCompact (KLev F n M : Set (GL (Fin n) (Af F))) :=
  (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL F n).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_KLev hM)) KLev_le_integral

end UpperTheory.V.Af
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RInv2
section
noncomputable section

open NumberField IsDedekindDomain Topology Matrix MeasureTheory GlobalTheory.CuspRep

namespace UpperTheory.V.InvT

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {a : ℕ}

theorem invT_val (g : GL (Fin a) R) : (invT a R g).val = (g⁻¹).valᵀ := rfl

theorem invT_inv_val (g : GL (Fin a) R) : ((invT a R g)⁻¹).val = g.valᵀ := rfl

@[simp] theorem invT_invT (g : GL (Fin a) R) : invT a R (invT a R g) = g := Units.ext (Matrix.transpose_transpose _)

theorem map_invT (f : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map f (invT a R g) = invT a S (GeneralLinearGroup.map f g) := Units.ext rfl

theorem cornerGL_invT (s : R →ₙ+* S) (g : GL (Fin a) R) : cornerGL a s (invT a R g) = invT a S (cornerGL a s g) := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s ((g⁻¹).val j i) =
    (1 : Matrix (Fin a) (Fin a) S) j i - s ((1 : Matrix (Fin a) (Fin a) R) j i) + s ((g⁻¹).val j i)
  simp only [Matrix.one_apply, eq_comm (a := i)]

theorem det_invT (g : GL (Fin a) R) : GeneralLinearGroup.det (invT a R g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  exact Units.ext (Matrix.det_transpose _)

theorem continuous_invT [TopologicalSpace R] : Continuous (invT a R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

def revGL (a : ℕ) (R : Type) [CommRing R] : GL (Fin a) R :=
  ⟨(1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id, (1 : Matrix (Fin a) (Fin a) R).submatrix id Fin.revPerm,
    by rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]; simp,
    by rw [Matrix.submatrix_mul_equiv]; simp⟩

theorem map_revGL (f : R →+* S) : GeneralLinearGroup.map f (revGL a R) = revGL a S := by
  ext i j
  change f ((1 : Matrix (Fin a) (Fin a) R) _ _) = (1 : Matrix (Fin a) (Fin a) S) _ _
  simp [Matrix.one_apply, apply_ite f]

def blockRev {r : ℕ} : BlockIx a (a - r) ≃ BlockIx a r where
  toFun p := ⟨(p.1.2.rev, p.1.1.rev), by have := p.2; have := p.1.1.2; have := p.1.2.2; simp only [Fin.val_rev]; omega⟩
  invFun p := ⟨(p.1.2.rev, p.1.1.rev), by have := p.2; have := p.1.1.2; have := p.1.2.2; simp only [Fin.val_rev]; omega⟩
  left_inv p := by simp
  right_inv p := by simp

theorem revGL_mul_invT_unip {r : ℕ} (x : BlockIx a r → R) :
    revGL a R * invT a R (unip x) = unip (fun p : BlockIx a (a - r) => -x (blockRev p)) * revGL a R := by
  apply Units.ext
  change (1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id * (1 - nilM x)ᵀ =
    (1 + nilM fun p : BlockIx a (a - r) => -x (blockRev p)) * (1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id
  ext i j
  have h1 : ∀ M : Matrix (Fin a) (Fin a) R,
      ((1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id * M) i j = M i.rev j := fun M => by
    simp [Matrix.mul_apply, Matrix.one_apply]
  have h2 : ∀ M : Matrix (Fin a) (Fin a) R,
      (M * (1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id) i j = M i j.rev := fun M => by
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.rev_eq_iff]
  rw [h1, h2]
  have hi := i.2
  have hj := j.2
  simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, nilM, Matrix.of_apply]
  rw [sub_eq_add_neg]
  congr 1
  · exact if_congr (by rw [eq_comm, Fin.rev_eq_iff]) rfl rfl
  · by_cases h : (j : ℕ) < r ∧ r ≤ (i.rev : ℕ)
    · rw [dite_eq_left h, dite_eq_left (by simp only [Fin.val_rev] at h ⊢; omega)]
      simp [blockRev]
    · rw [dite_eq_right h, dite_eq_right (by simp only [Fin.val_rev] at h ⊢; omega), neg_zero]

end Ring

section Smooth

open scoped ContDiff

variable {A : Type} [NormedCommRing A] [NormedAlgebra ℝ A] {a : ℕ}

def invTL (x : Fin a → Fin a → A) : Fin a → Fin a → A := Matrix.of.symm ((Matrix.of x)⁻¹)ᵀ

omit [NormedAlgebra ℝ A] in
theorem invTL_val (y : GL (Fin a) A) : invTL (Matrix.of.symm y.val) = Matrix.of.symm (invT a A y).val :=
  congrArg (fun m : Matrix (Fin a) (Fin a) A => Matrix.of.symm mᵀ) (Matrix.coe_units_inv y).symm

omit [NormedAlgebra ℝ A] in
theorem invTL_one : invTL (Matrix.of.symm (1 : Matrix (Fin a) (Fin a) A)) = Matrix.of.symm 1 :=
  (invTL_val 1).trans (by rw [map_one]; rfl)

omit [NormedAlgebra ℝ A] in
theorem isUnit_invTL {x : Fin a → Fin a → A} (hx : IsUnit (Matrix.of x)) : IsUnit (Matrix.of (invTL x)) := by
  obtain ⟨u, hu⟩ := hx
  have e : x = Matrix.of.symm u.val := hu.symm
  rw [e, invTL_val]
  exact (invT a A u).isUnit


omit [NormedAlgebra ℝ A] in
theorem norm_transpose (x : Matrix (Fin a) (Fin a) A) : ‖Matrix.of.symm xᵀ‖ = ‖Matrix.of.symm x‖ := by
  have h : ∀ x : Matrix (Fin a) (Fin a) A, ‖Matrix.of.symm xᵀ‖ ≤ ‖Matrix.of.symm x‖ := fun x =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j =>
      (norm_le_pi_norm (Matrix.of.symm x j) i).trans (norm_le_pi_norm (Matrix.of.symm x) j)
  exact le_antisymm (h x) (h xᵀ)

private theorem contDiff_det : ContDiff ℝ ∞ fun x : Fin a → Fin a → A => (Matrix.of x).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact (contDiff_apply ℝ _ i).comp (contDiff_apply ℝ _ (σ i))

variable [CompleteSpace A]

theorem contDiffAt_invTL {x : Fin a → Fin a → A} (hx : IsUnit (Matrix.of x)) : ContDiffAt ℝ ∞ invTL x := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hx
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  have e : (fun x : Fin a → Fin a → A => invTL x i j) = fun x =>
      Ring.inverse (Matrix.of x).det * (Matrix.of (Function.update x i (Pi.single j 1))).det := by
    funext x
    change (Matrix.of x)⁻¹ j i = _
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply]
    rfl
  rw [e]
  refine ContDiffAt.mul (ContDiffAt.comp (g := Ring.inverse) x (hu ▸ contDiffAt_ringInverse ℝ u) contDiff_det.contDiffAt)
    (contDiff_det.comp (contDiff_pi.2 fun k => ?_)).contDiffAt
  by_cases h : k = i
  · subst h; simpa using contDiff_const
  · simpa [h] using contDiff_apply ℝ _ k

theorem fderiv_invTL_one (X : Fin a → Fin a → A) :
    fderiv ℝ invTL (Matrix.of.symm (1 : Matrix (Fin a) (Fin a) A)) X = Matrix.of.symm (-(Matrix.of X)ᵀ) := by
  set o : Fin a → Fin a → A := Matrix.of.symm (1 : Matrix (Fin a) (Fin a) A) with ho
  have hd : HasFDerivAt invTL (fderiv ℝ invTL o) o :=
    ((contDiffAt_invTL (x := o) isUnit_one).differentiableAt (by simp)).hasFDerivAt
  funext i j
  have h1 : ∀ k, HasFDerivAt (fun x : Fin a → Fin a → A => x k i) _ o := fun k =>
    hasFDerivAt_pi'.1 (hasFDerivAt_pi'.1 (hasFDerivAt_id (𝕜 := ℝ) o) k) i
  have h2 : ∀ k, HasFDerivAt (fun x : Fin a → Fin a → A => invTL x k j) _ o := fun k =>
    hasFDerivAt_pi'.1 (hasFDerivAt_pi'.1 hd k) j
  have h3 := HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => (h1 k).mul' (h2 k)
  have hu : ∀ᶠ x : Fin a → Fin a → A in 𝓝 o, IsUnit (Matrix.of x).det :=
    (Units.isOpen.preimage contDiff_det.continuous).mem_nhds ((Matrix.isUnit_iff_isUnit_det _).1 isUnit_one)
  have h4 : HasFDerivAt (𝕜 := ℝ) (fun x : Fin a → Fin a → A => ∑ k, x k i * invTL x k j) 0 o := by
    refine (hasFDerivAt_const ((1 : Matrix (Fin a) (Fin a) A) i j) o).congr_of_eventuallyEq (hu.mono fun x hx => ?_)
    have := congrFun (congrFun (congrArg Matrix.transpose (Matrix.nonsing_inv_mul _ hx)) i) j
    rwa [Matrix.transpose_mul, Matrix.transpose_one] at this
  have h5 := congrArg (fun L : (Fin a → Fin a → A) →L[ℝ] A => L X) (h3.unique h4)
  have e : invTL o = o := invTL_one
  have e' : ∀ k l, o k l = if k = l then 1 else 0 := fun k l => Matrix.one_apply
  simp [e, e', Finset.sum_add_distrib] at h5
  exact eq_neg_of_add_eq_zero_left h5

end Smooth

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem ratGL_invT (γ : GL (Fin a) E) : ratGL E a (invT a E γ) = invT a (Ad E) (ratGL E a γ) := map_invT _ γ

theorem finGL_invT (k : GL (Fin a) (Af E)) : finGL E a (invT a (Af E) k) = invT a (Ad E) (finGL E a k) :=
  cornerGL_invT _ k

theorem locGL_invT (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    locGL E a w (invT a _ g) = invT a (Af E) (locGL E a w g) := cornerGL_invT _ g

theorem chiDet_invT (χ : Formalism.L2.Host.HChar E) (g : GA E a) : chiDet a χ (invT a (Ad E) g) = chiDet a χ⁻¹ g :=
  (congrArg χ.1 (det_invT g)).trans (map_inv χ.1 _)

theorem isCuspidal_invT {φ : GA E a → ℂ} (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g) (h : IsCuspidal φ) :
    IsCuspidal fun g => φ (invT a (Ad E) g) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  borelize (BlockIx a (a - r) → Ad E)
  let e : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a (a - r) → Ad E) :=
    { toFun := fun x p => -x (blockRev p)
      invFun := fun y p => -y (blockRev.symm p)
      left_inv := fun x => by funext p; simp
      right_inv := fun x => by funext p; simp
      map_add' := fun x y => by funext p; simp [add_comm]
      continuous_toFun := continuous_pi fun p => (continuous_apply _).neg
      continuous_invFun := continuous_pi fun p => (continuous_apply _).neg }
  let em : (BlockIx a r → Ad E) ≃ᵐ (BlockIx a (a - r) → Ad E) := e.toHomeomorph.toMeasurableEquiv
  have hμ' : (μ.map em).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let er : ratN E a (a - r) ≃ ratN E a r :=
    { toFun := fun y => ⟨e.symm y.1, by
        obtain ⟨_, y, rfl⟩ := y
        exact ⟨fun p => -y (blockRev.symm p), funext fun p => map_neg (algebraMap E (Ad E)) _⟩⟩
      invFun := fun y => ⟨e y.1, by
        obtain ⟨_, y, rfl⟩ := y
        exact ⟨fun p => -y (blockRev p), funext fun p => map_neg (algebraMap E (Ad E)) _⟩⟩
      left_inv := fun y => Subtype.ext (e.apply_symm_apply _)
      right_inv := fun y => Subtype.ext (e.symm_apply_apply _) }
  have hF' : IsAddFundamentalDomain (ratN E a (a - r)) (em '' 𝓕) (μ.map em) :=
    hF.image_of_equiv em.toEquiv
      (MeasurePreserving.symm em ⟨em.measurable, rfl⟩).quasiMeasurePreserving er fun y x => by
        change e (e.symm y.1 + x) = y.1 + e x
        rw [map_add (f := _), e.apply_symm_apply]
  have key := h (a - r) (by omega) (by omega) _ _ hμ' hF' (revGL a (Ad E) * invT a (Ad E) g)
  rw [setIntegral_map_equiv, Set.preimage_image_eq _ em.injective] at key
  rw [← key]
  refine congrArg _ (funext fun x => ?_)
  beta_reduce
  rw [map_mul, ← hl (revGL a E), ratGL, map_revGL, ← mul_assoc, revGL_mul_invT_unip, mul_assoc]
  rfl

theorem hasSatGL_invT {w : HeightOneSpectrum (𝓞 E)} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' g (T x) = T (ρ (invT a _ g) x)) {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w ρ B) :
    GlobalTheory.LFun.HasSatGL w ρ' (B.map (·⁻¹)) := by
  let c := GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl (w.adicCompletion E)) a
  have hc : ∀ g, c g = invT a _ g := fun g => Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)
  have hs : ∀ g, c.symm g = invT a _ g := fun g => (MulEquiv.symm_apply_eq _).2 (by rw [hc, invT_invT])
  have hK := GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) (RingEquiv.refl (w.adicCompletion E)) (O := Formalism.UG.Ov E w)
    (O' := Formalism.UG.Ov E w) fun _ => Iff.rfl
  have hf : ∀ g y, T.toLinearMap ((ρ.comp c.symm.toMonoidHom) g y) = ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ (c.symm g) y) = ρ' g (T y)
    rw [hs, hT]
  have key : ∀ x, GlobalTheory.LFun.IsSatVecGL w ρ x B → GlobalTheory.LFun.IsSatVecGL w ρ' (T x) (B.map (·⁻¹)) := fun x hx =>
    (GlobalTheory.LFun.ConjPlace.isSatVecGL_invT (.refl _) (fun _ => rfl) rfl hx).map T.toLinearMap hf
      ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hT, show GlobalTheory.LFun.ConjPlace.invT _ a k = _ from hc k, invT_invT] at this

end UpperTheory.V.InvT
end
end

