module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.DimPosOfHasType

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousLvMat
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT bc)
open scoped TensorProduct NNReal

namespace GlobalTheory.SphEisModel

open GlobalTheory.SphEis
open Formalism.UG (cT_mul cT_one)

section Ring

variable {A : Type} [CommRing A] {s : A →+* A} {n j m : ℕ} {J : Matrix (Fin n) (Fin n) A}
  {C D C' D' : Matrix (Fin n) (Fin j) A} {Z Z' : Matrix (Fin n) (Fin m) A} {J₀ Ji : Matrix (Fin m) (Fin m) A}

theorem cT_add {p q : Type} (X Y : Matrix p q A) : cT s (X + Y) = cT s X + cT s Y := by ext; simp [cT]
theorem cT_cT (h : ∀ x, s (s x) = x) {p q : Type} (X : Matrix p q A) : cT s (cT s X) = X := by ext; simp [cT, h]


variable (s J) in
def Gram (C D : Matrix (Fin n) (Fin j) A) (Z : Matrix (Fin n) (Fin m) A) (J₀ : Matrix (Fin m) (Fin m) A) : Prop :=
  cT s C * (J * C) = 0 ∧ cT s C * (J * Z) = 0 ∧ cT s C * (J * D) = 1 ∧
  cT s Z * (J * C) = 0 ∧ cT s Z * (J * Z) = J₀ ∧ cT s Z * (J * D) = 0 ∧
  cT s D * (J * C) = 1 ∧ cT s D * (J * Z) = 0 ∧ cT s D * (J * D) = 0


variable (s J C D Z Ji) in
def carry (C' D' : Matrix (Fin n) (Fin j) A) (Z' : Matrix (Fin n) (Fin m) A) : Matrix (Fin n) (Fin n) A :=
  C' * (cT s D * J) + Z' * (Ji * (cT s Z * J)) + D' * (cT s C * J)

theorem carry_frame (g : Gram s J C D Z J₀) (hi : Ji * J₀ = 1) :
    carry s J C D Z Ji C' D' Z' * C = C' ∧ carry s J C D Z Ji C' D' Z' * Z = Z' ∧ carry s J C D Z Ji C' D' Z' * D = D' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := g
  simp [carry, Matrix.add_mul, Matrix.mul_assoc, *]

theorem rext (hs : carry s J C D Z Ji C D Z = 1) {p : ℕ} {X Y : Matrix (Fin p) (Fin n) A} (h1 : X * C = Y * C)
    (h2 : X * Z = Y * Z) (h3 : X * D = Y * D) : X = Y := by
  rw [← Matrix.mul_one X, ← Matrix.mul_one Y, ← hs]
  simp only [carry, Matrix.mul_add, ← Matrix.mul_assoc, h1, h2, h3]

theorem lext (hs : carry s J C D Z Ji C D Z = 1) {p : ℕ} {X Y : Matrix (Fin n) (Fin p) A} (h1 : cT s C * X = cT s C * Y)
    (h2 : cT s Z * X = cT s Z * Y) (h3 : cT s D * X = cT s D * Y) : X = Y := by
  rw [← Matrix.one_mul X, ← Matrix.one_mul Y, ← cT_one s, ← hs]
  simp only [carry, cT_add, cT_mul s C, cT_mul s Z, cT_mul s D, Matrix.add_mul, Matrix.mul_assoc, h1, h2, h3]

theorem unitary (g : Gram s J C D Z J₀) (g' : Gram s J C' D' Z' J₀) (hs : carry s J C D Z Ji C D Z = 1)
    {M : Matrix (Fin n) (Fin n) A} (e1 : M * C = C') (e2 : M * Z = Z') (e3 : M * D = D') : cT s M * J * M = J := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := g
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := g'
  have a : ∀ {p q : ℕ} (U : Matrix (Fin n) (Fin p) A) (V : Matrix (Fin n) (Fin q) A),
      cT s U * (cT s M * J * M * V) = cT s (M * U) * (J * (M * V)) := fun U V => by
    simp only [cT_mul, Matrix.mul_assoc]
  refine rext hs (lext hs ?_ ?_ ?_) (lext hs ?_ ?_ ?_) (lext hs ?_ ?_ ?_) <;> rw [a] <;> simp only [*]

theorem gram_levi (hs : ∀ x, s (s x) = x) (g : Gram s J C D Z J₀) (α : GL (Fin j) A) :
    Gram s J (C * α.1) (D * cT s (α⁻¹).1) Z J₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := g
  have a : ∀ {p q p' q' : ℕ} (U : Matrix (Fin n) (Fin p) A) (V : Matrix (Fin n) (Fin q) A) (x : Matrix (Fin p) (Fin p') A)
      (y : Matrix (Fin q) (Fin q') A), cT s (U * x) * (J * (V * y)) = cT s x * (cT s U * (J * V)) * y := fun U V x y => by
    simp only [cT_mul, Matrix.mul_assoc]
  have b : ∀ {p q q' : ℕ} (U : Matrix (Fin n) (Fin p) A) (V : Matrix (Fin n) (Fin q) A)
      (y : Matrix (Fin q) (Fin q') A), cT s U * (J * (V * y)) = (cT s U * (J * V)) * y := fun U V y => by
    simp only [Matrix.mul_assoc]
  have c : ∀ {p q p' : ℕ} (U : Matrix (Fin n) (Fin p) A) (V : Matrix (Fin n) (Fin q) A) (x : Matrix (Fin p) (Fin p') A),
      cT s (U * x) * (J * V) = cT s x * (cT s U * (J * V)) := fun U V x => by
    simp only [cT_mul, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, h5, ?_, ?_, ?_, ?_⟩
  · rw [a, h1]; simp
  · rw [c, h2]; simp
  · rw [a, h3, Matrix.mul_one, ← cT_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, cT_one]
  · rw [b, h4]; simp
  · rw [b, h6]; simp
  · rw [a, h7, Matrix.mul_one, cT_cT hs, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · rw [c, h8]; simp
  · rw [a, h9]; simp

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n j m : ℕ} {J : Matrix (Fin n) (Fin n) E} {C D : Matrix (Fin n) (Fin j) E}
  {Z : Matrix (Fin n) (Fin m) E} {J₀ : Matrix (Fin m) (Fin m) E}

omit [NumberField E] in
theorem ad_cT {p q : Type} (X : Matrix p q E) : adMat F (cT (σ : E →+* E) X) = cT (sigR (AF F) σ) (adMat F X) := by
  ext a b; simp [cT, sigR, inclR]

theorem sig_sig (h : IsCMExt F E σ) (x : AF F ⊗[F] E) : sigR (AF F) σ (sigR (AF F) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, sigma_sigma h]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem gram_rat (f : Fr σ J C D Z J₀) : Gram (σ : E →+* E) J C D Z J₀ := by
  simp only [Gram, ← Matrix.mul_assoc]
  exact ⟨f.cc, f.cz, f.cd, f.zc, f.zz, f.zd, f.dc, f.dz, f.dd⟩

theorem gram_ad (f : Fr σ J C D Z J₀) :
    Gram (sigR (AF F) σ) (JR (AF F) J) (adMat F C) (adMat F D) (adMat F Z) (adMat F J₀) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := gram_rat f
  simp only [Gram, JR, ← ad_cT, ← Matrix.map_mul, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  simp

omit [NumberField E] in
theorem ad_carry (Ji : Matrix (Fin m) (Fin m) E) (C' D' : Matrix (Fin n) (Fin j) E) (Z' : Matrix (Fin n) (Fin m) E) :
    adMat F (carry (σ : E →+* E) J C D Z Ji C' D' Z') = carry (sigR (AF F) σ) (JR (AF F) J) (adMat F C) (adMat F D) (adMat F Z)
      (adMat F Ji) (adMat F C') (adMat F D') (adMat F Z') := by
  simp only [carry, JR, ← ad_cT, ← Matrix.map_mul]
  ext; simp only [Matrix.map_apply, Matrix.add_apply, map_add (f := _)]

theorem sum_ad (f : Fr σ J C D Z J₀) : carry (sigR (AF F) σ) (JR (AF F) J) (adMat F C) (adMat F D) (adMat F Z)
      (adMat F J₀⁻¹) (adMat F C) (adMat F D) (adMat F Z) = 1 := by
  rw [← ad_carry, show carry (σ : E →+* E) J C D Z J₀⁻¹ C D Z = 1 from f.sum]
  simp

theorem inv_mul₀ (f : Fr σ J C D Z J₀) : J₀⁻¹ * J₀ = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit f.herm₀.2)
theorem inv_mul_ad (f : Fr σ J C D Z J₀) : adMat F J₀⁻¹ * adMat F J₀ = 1 := by rw [← Matrix.map_mul, inv_mul₀ f]; simp

def lvMat (f : Fr σ J C D Z J₀) : GL (Fin j) (AF F ⊗[F] E) →* Matrix (Fin n) (Fin n) (AF F ⊗[F] E) where
  toFun α := carry (sigR (AF F) σ) (JR (AF F) J) (adMat F C) (adMat F D) (adMat F Z) (adMat F J₀⁻¹)
    (adMat F C * α.1) (adMat F D * cT (sigR (AF F) σ) (α⁻¹).1) (adMat F Z)
  map_one' := by simpa [cT_one] using sum_ad f
  map_mul' α β := by
    have h := fun C' D' Z' => carry_frame (C' := C') (D' := D') (Z' := Z') (gram_ad f) (inv_mul_ad f)
    refine rext (sum_ad f) ?_ ?_ ?_
    · rw [Matrix.mul_assoc, (h _ _ _).1, (h _ _ _).1, ← Matrix.mul_assoc, (h _ _ _).1, Units.val_mul, Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, (h _ _ _).2.1, (h _ _ _).2.1, (h _ _ _).2.1]
    · rw [Matrix.mul_assoc, (h _ _ _).2.2, (h _ _ _).2.2, ← Matrix.mul_assoc, (h _ _ _).2.2, _root_.mul_inv_rev, Units.val_mul,
        cT_mul, Matrix.mul_assoc]

theorem lvMat_frame (f : Fr σ J C D Z J₀) (α : GL (Fin j) (AF F ⊗[F] E)) :
    lvMat f α * adMat F C = adMat F C * α.1 ∧ lvMat f α * adMat F Z = adMat F Z ∧
      lvMat f α * adMat F D = adMat F D * cT (sigR (AF F) σ) (α⁻¹).1 := carry_frame (gram_ad f) (inv_mul_ad f)

theorem continuous_lvMat (f : Fr σ J C D Z J₀) : Continuous (lvMat f) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : Continuous (sigR (AF F) σ) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F)
      (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ).toLinearMap
  have h1 : Continuous fun α : GL (Fin j) (AF F ⊗[F] E) => cT (sigR (AF F) σ) (α⁻¹).1 :=
    (Units.continuous_coe_inv.matrix_map hs).matrix_transpose
  exact (((continuous_const.matrix_mul Units.continuous_val).matrix_mul continuous_const).add continuous_const).add
    ((continuous_const.matrix_mul h1).matrix_mul continuous_const)

def lv (f : Fr σ J C D Z J₀) : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J :=
  (lvMat f).toHomUnits.codRestrict (HR (AF F) σ J) fun α =>
    unitary (gram_ad f) (gram_levi (sig_sig f.cm) (gram_ad f) α) (sum_ad f) (lvMat_frame f α).1 (lvMat_frame f α).2.1
      (lvMat_frame f α).2.2

theorem isLv_lv (f : Fr σ J C D Z J₀) : IsLv σ J C D Z (lv f) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine ⟨?_, fun α => (lvMat_frame f α).1, fun α => (lvMat_frame f α).2.2, fun α => (lvMat_frame f α).2.1, fun δ => ?_⟩
  · refine (isEmbedding_matHom (AF F) σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨continuous_lvMat f, ?_⟩)
    exact (continuous_lvMat f).comp continuous_inv
  · have h := fun C' D' Z' => carry_frame (C' := C') (D' := D') (Z' := Z') (gram_rat f) (inv_mul₀ f)
    set M := carry (σ : E →+* E) J C D Z J₀⁻¹ (C * δ.1) (D * cT (σ : E →+* E) (δ⁻¹).1) Z with hM
    have hu : cT (σ : E →+* E) M * J * M = J :=
      unitary (gram_rat f) (gram_levi (sigma_sigma f.cm) (gram_rat f) δ) f.sum (h _ _ _).1 (h _ _ _).2.1 (h _ _ _).2.2
    have hd : M.det ≠ 0 := fun e => f.herm.2 (by rw [← hu, Matrix.det_mul, e, mul_zero])
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hd, hu, Units.ext ?_⟩
    change adMat F M = carry _ _ _ _ _ _ (adMat F C * adMat F δ.1) (adMat F D * cT _ (adMat F (δ⁻¹).1)) _
    rw [hM, ad_carry, ← ad_cT, ← Matrix.map_mul, ← Matrix.map_mul]

theorem isLv_unique (f : Fr σ J C D Z J₀) {l l' : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J} (h : IsLv σ J C D Z l)
    (h' : IsLv σ J C D Z l') : l = l' := by
  ext α
  exact matHom_injective _ σ J (Units.ext (rext (sum_ad f) ((h.onC α).trans (h'.onC α).symm) ((h.onZ α).trans (h'.onZ α).symm)
    ((h.onD α).trans (h'.onD α).symm)))

theorem isLv_injective (f : Fr σ J C D Z J₀) {l : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J} (h : IsLv σ J C D Z l) :
    Function.Injective l := fun α β e => by
  have h7 := (gram_ad f).2.2.2.2.2.2.1
  have := congrArg (fun X : Matrix (Fin n) (Fin j) (AF F ⊗[F] E) => cT (sigR (AF F) σ) (adMat F D) * (JR (F := F) (AF F) J * X))
    ((h.onC α).symm.trans (e ▸ h.onC β))
  simp only [← Matrix.mul_assoc] at this h7
  rw [h7, Matrix.one_mul, Matrix.one_mul] at this
  exact Units.ext this

end GlobalTheory.SphEisModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsGramOneZero
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.Model

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CM

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem ιMulti_comb {m : ℕ} (b : Fin m → V) (c : Matrix (Fin m) (Fin m) K) :
    exteriorPower.ιMulti K m (fun i => ∑ j, c i j • b j) = c.det • exteriorPower.ιMulti K m b := by
  have h : (exteriorPower.ιMulti K m).compLinearMap (Fintype.linearCombination K b) =
      (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K).smulRight (exteriorPower.ιMulti K m b) := by
    refine (Pi.basisFun K (Fin m)).ext_alternating fun v hv => ?_
    let s : Equiv.Perm (Fin m) := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hv)
    have e : (fun i => Pi.basisFun K (Fin m) (v i)) = (fun i => Pi.basisFun K (Fin m) i) ∘ s := rfl
    rw [e, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e1 : (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K) (fun i => Pi.basisFun K (Fin m) i) = 1 := by
      change Matrix.det (Matrix.of fun i => Pi.basisFun K (Fin m) i) = 1
      rw [show (Matrix.of fun i => Pi.basisFun K (Fin m) i) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]
    rw [AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp [Pi.basisFun_apply, Fintype.linearCombination_apply_single]
  exact AlternatingMap.congr_fun h c


omit [NumberField K] in
theorem ιMulti_comb_int {m : ℕ} (b : Fin m → V) (c : Matrix (Fin m) (Fin m) (𝓞 K)) :
    exteriorPower.ιMulti K m (fun i => ∑ j, c i j • b j) = algebraMap (𝓞 K) K c.det • exteriorPower.ιMulti K m b := by
  have := ιMulti_comb b (c.map (algebraMap (𝓞 K) K))
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
  rw [← this]
  congr 1
  funext i
  exact Finset.sum_congr rfl fun j _ => (algebraMap_smul K _ _).symm


omit [NumberField K] in
theorem detSpan_span {m : ℕ} (b : Fin m → V) :
    detSpan K m (Submodule.span (𝓞 K) (Set.range b)) = Submodule.span (𝓞 K) {exteriorPower.ιMulti K m b} := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨y, hy, rfl⟩
    choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hy i)
    rw [show y = fun i => ∑ j, (Matrix.of c) i j • b j from funext fun i => (hc i).symm, ιMulti_comb_int]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩
  · rintro _ rfl
    exact ⟨b, fun i => Submodule.subset_span ⟨i, rfl⟩, rfl⟩



end Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ}

end GlobalTheory.FlatCM.Model

end
end

