module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjStable
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0048
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem idx_GK {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (Om l)) :
    K.fixingSubgroup.index = finrank ℚ_[l] K :=
  (IntermediateField.finrank_eq_fixingSubgroup_index (Om l) K).symm

private theorem sup_Iq {l : ℕ} [Fact l.Prime] (K : FinExt l) :
    GK K ⊔ Iq l = (K0 K).fixingSubgroup := by
  haveI := K.2
  have ho : IsOpen ((GK K ⊔ Iq l : Subgroup (GQ l)) : Set (GQ l)) :=
    Subgroup.isOpen_mono le_sup_left (IntermediateField.fixingSubgroup_isOpen K.1)
  have hc := Subgroup.isClosed_of_isOpen _ ho
  have h1 := InfiniteGalois.fixingSubgroup_fixedField (k := ℚ_[l]) (K := Om l) ⟨GK K ⊔ Iq l, hc⟩
  have h2 : IntermediateField.fixedField (GK K ⊔ Iq l) = K0 K := by
    apply le_antisymm
    · refine le_inf ?_ ?_
      · rw [← InfiniteGalois.fixedField_fixingSubgroup K.1]
        exact IntermediateField.fixedField_le le_sup_left
      · rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l)]
        exact IntermediateField.fixedField_le le_sup_right
    · rw [IntermediateField.le_iff_le]
      exact sup_le (IntermediateField.fixingSubgroup_le inf_le_left)
        (IntermediateField.fixingSubgroup_le inf_le_right)
  rw [← h2]
  exact h1.symm

theorem UpperTheory.V.Loc.isCrIff :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (ρ : Representation A ↥(GK K) V), (IsCr (GK K).subtype ρ ↔ Crys K ρ) ∧ (IsDr (GK K).subtype ρ ↔ DeRham K ρ) := by
  intro l _ K A _ _ V _ _ _ _ ρ
  have hC : Dcr (GK K).subtype (resCoef ℚ_[l] ρ) = Dcris ((PP l).PD K) (resCoef ℚ_[l] ρ) := by
    unfold Dcr Dcris
    refine iInf_congr fun g => ?_
    have : actC (GK K).subtype (resCoef ℚ_[l] ρ) g = actVB ((PP l).PD K) (resCoef ℚ_[l] ρ) g := by
      unfold actC actVB
      congr 1
      ext b
      exact ((PP l).PD_actB K g b).symm
    rw [this]
  have hD : Ddr (GK K).subtype (resCoef ℚ_[l] ρ) = DdR ((PP l).PD K) (resCoef ℚ_[l] ρ) := by
    unfold Ddr DdR
    refine iInf_congr fun g => ?_
    have : actD (GK K).subtype (resCoef ℚ_[l] ρ) g = actVdR ((PP l).PD K) (resCoef ℚ_[l] ρ) g := by
      unfold actD actVdR
      congr 1
      ext b
      exact ((PP l).PD_actdR K g b).symm
    rw [this]
  constructor
  · unfold IsCr Crys IsCrys
    rw [hC, Subgroup.range_subtype, sup_Iq, idx_GK]
  · unfold IsDr DeRham IsDR
    rw [hD, Subgroup.range_subtype, show (GK K).index = finrank ℚ_[l] K.1 from idx_GK K.1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
section
noncomputable section

namespace UpperTheory.V.Loc

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing

structure Dat3 (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] where
  η : GQ l →* ℤˣ
  Ψ : GQ l →* Oˣ
  τ : GQ l →* Oˣ
  e : ℕ
  Kv : FinExt l
  odd : l ≠ 2
  e_pos : 1 ≤ e
  η_ker : ∀ g, η g = 1 ↔ g ∈ GK Kv
  η_unr : ∀ g ∈ Iq l, η g = 1
  τ_open : IsOpen (τ.ker : Set (GQ l))
  Ψ_cont : AdicCont (maximalIdeal O) fun g => (Ψ g : O)
  Ψ_I : ∀ g ∈ Iq l, Ψ g = cycA l l O g ^ e * τ g

def hodge0 (e : ℕ) (i : ℤ) : ℕ := if i = -(e : ℤ) ∨ i = 0 ∨ i = e then 1 else 0

namespace Dat3

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O)

def HL : Subgroup (GQ l) := D.η.ker ⊓ D.τ.ker

def rz (A : Type) [CommRing A] [Algebra O A] : GQ l →* GG (m := 3) (R := A) :=
  (GG.map (algebraMap O A)).comp (r0 D.η D.Ψ)

section Types

variable {B : Type} [CommRing B] [Algebra O B] [Algebra ℚ_[l] B]

def IsType (r : GQ l →* GG (m := 3) (R := B)) : Prop :=
  ∃ ρ : ↥(GK D.Kv) →* GL (Fin 3) B, (∀ g, ρ g = (r g).left) ∧
    PotCrysType D.Kv (colRep ρ) 3 (hodge0 D.e)
      fun γ => algebraMap O B ((D.τ γ : O) + 1 + (((D.τ γ)⁻¹ : Oˣ) : O))

def IsLCr (r : GQ l →* GG (m := 3) (R := B)) : Prop :=
  ∃ ρ : ↥D.HL →* GL (Fin 3) B, (∀ g, ρ g = (r g).left) ∧ IsCr D.HL.subtype (colRep ρ)

variable {E : Type} [CommRing E] [Algebra O E] (π : B →+* E)

structure InDcrAt (r₁ : GQ l →* GG (m := 3) (R := E))
    (r : GQ l →* GG (m := 3) (R := B)) : Prop where
  mult : HasMult D.η r
  red : (GG.map π).comp r = r₁
  cont : ∀ a b, QCont l fun g => (r g).mat a b
  cr : D.IsLCr r

abbrev InDcr (r : GQ l →* GG (m := 3) (R := B)) : Prop := D.InDcrAt π (D.rz E) r

structure InDtri (r : GQ l →* GG (m := 3) (R := B)) : Prop extends D.InDcrAt π (D.rz E) r where
  tri : ∀ g a b, wt a b < 0 → (r g).mat a b = 0

def InDord (r : GQ l →* GG (m := 3) (R := B)) : Prop :=
  ∃ (u : GQ l →* GG (m := 3) (R := B)) (n : GL (Fin 3) B), D.InDtri π u ∧ CongOne (RingHom.ker π) n ∧
    (∀ a b, 0 ≤ wt a b → ((n : Matrix (Fin 3) (Fin 3) B) - 1) a b = 0) ∧ r = conjBy n u

end Types

abbrev Univ : Type 1 := U3.Univ (GCond.noCondition O D.η D.Ψ)

section Ord

open Polynomial

def IsInertiaInfiniteCyclotomic (s : GQ l) : Prop := s ∈ D.HL ∧ s ∈ Iq l ∧ ¬ IsOfFinOrder (cyc l l s)

def IsFr (σ : GQ l) : Prop :=
  (∃ h : σ ∈ D.HL, ((Iq l).comap D.HL.subtype ⊔ Subgroup.zpowers (⟨σ, h⟩ : ↥D.HL)).topologicalClosure = ⊤) ∧
    ∃ (σ₀ : GQ l) (m : ℕ), IsFrob σ₀ ∧ 1 ≤ m ∧ (σ₀ ^ m)⁻¹ * σ ∈ Iq l

def s0 : GQ l := Classical.epsilon (IsInertiaInfiniteCyclotomic D)

def fr : GQ l := Classical.epsilon (IsFr D)

def cc (a : Fin 3) : O :=
  (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (s0 D) - UpperTheory.V.UnitaryThreeInertia.psi D.Ψ (a + 1) (s0 D)) *
    (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (s0 D) - UpperTheory.V.UnitaryThreeInertia.psi D.Ψ (a + 2) (s0 D))

section Eq

variable {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C))

def sh (a : Fin 3) (s : GQ l) : Matrix (Fin 3) (Fin 3) C :=
  (r s).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))

def ordIdeal : Ideal C :=
  Ideal.span ({x | ∃ s ∈ D.HL ⊓ Iq l, ∃ i : ℕ, x = ((r s).mat.charpoly -
      ∏ a, (X - Polynomial.C (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i} ∪
    {x | ∃ s : Fin 3 → GQ l, (∀ a, s a ∈ D.HL ⊓ Iq l) ∧ ∃ i j,
      x = (sh D r 0 (s 0) * sh D r 1 (s 1) * sh D r 2 (s 2)) i j})

def tr (a : Fin 3) : C := (sh D r (a + 1) (s0 D) * sh D r (a + 2) (s0 D) * (r (fr D)).mat).trace

def dd (a : Fin 3) : C :=
  algebraMap O C (cc D (a + 1)) * tr D r a - algebraMap O C ((cycA l l O (fr D) : Oˣ) * cc D a) * tr D r (a + 1)

def del : C := (l : C) * dd D r 0 * dd D r 1

end Eq

end Ord

variable (U : D.Univ)

def IY : Ideal U.R where
  carrier := {a | ∃ n : ℕ, del D U.r.hom ^ n * a ∈ ordIdeal D U.r.hom}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have e : del D U.r.hom ^ (m + n) * (a + b) = del D U.r.hom ^ n * (del D U.r.hom ^ m * a) +
        del D U.r.hom ^ m * (del D U.r.hom ^ n * b) := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hn)
  smul_mem' := by
    rintro c a ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ _ hn

def Icr : Ideal U.R := (IY D U).radical

def primesAt0 : Set (Ideal U.R) :=
  {P | P ∈ (D.Icr U).minimalPrimes ∧ ∀ x : U.R →ₐ[O] O, push x U.r.hom = r0 D.η D.Ψ → P ≤ RingHom.ker x}

def It : Ideal U.R := sInf (D.primesAt0 U)

abbrev Rt : Type := U.R ⧸ D.It U

def On {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) : Prop :=
  ∃ f : U.R →ₐ[O] C, push f U.r.hom = r ∧ D.It U ≤ RingHom.ker f

def PtsCr (J : Ideal U.R) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : U.R →ₐ[O] B),
    J ≤ RingHom.ker f → D.IsLCr (push f U.r.hom)

def CrPts (J : Ideal U.R) : Prop :=
  ∀ (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
    (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
    [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ f : U.R →ₐ[O] B,
    D.InDcr (π : B →+* E) (push f U.r.hom) → J ≤ RingHom.ker f

end Dat3

structure IsCompl {O R E σ : Type} [CommRing O] [CommRing R] [Algebra O R] [Field E] [Algebra O E]
    (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries σ E) : Prop where
  ker : RingHom.ker φ = I
  const : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)
  dense : ∀ (N : ℕ) (f : MvPowerSeries σ E), ∃ (a : R) (c : O), c ≠ 0 ∧
    c • f - φ a ∈ maximalIdeal (MvPowerSeries σ E) ^ N
  inj : ∀ (N : ℕ) (a : R), φ a ∈ maximalIdeal (MvPowerSeries σ E) ^ N →
    ∃ c : O, c ≠ 0 ∧ c • a ∈ RingHom.ker x ^ N ⊔ I

def DualDef {G E : Type} [Group G] [CommRing E] (r : G →* GG (m := 3) (R := E))
    (γ : G → Matrix (Fin 3) (Fin 3) E) (r' : G →* GG (m := 3) (R := DualNumber E)) : Prop :=
  ∀ g, (r' g).right = (r g).right ∧ ∀ a b, (r' g).mat a b = ⟨(r g).mat a b, (γ g * (r g).mat) a b⟩

end UpperTheory.V.Loc
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LineInv
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem coord_lTensor {K V B B' ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup B]
    [Module K B] [AddCommGroup B'] [Module K B'] [DecidableEq ι] (b : Basis ι K V) (f : B →ₗ[K] B')
    (x : V ⊗[K] B) (i : ι) :
    equivFinsuppOfBasisLeft b (LinearMap.lTensor V f x) i = f (equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp [equivFinsuppOfBasisLeft_apply_tmul_apply]
  | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz]

private theorem line_abs {K V B B' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup B]
    [Module K B] [AddCommGroup B'] [Module K B'] (φ : B →ₗ[K] B) (j : B →ₗ[K] B') (F : Submodule K B')
    (e : B) (he : e ≠ 0) (fund : ∀ y : B, φ y = y → j y ∈ F → ∃ c : K, c • e = y) (x : V ⊗[K] B)
    (h1 : LinearMap.lTensor V φ x = x)
    (h2 : ∃ z, LinearMap.lTensor V F.subtype z = LinearMap.lTensor V j x) :
    ∃! v : V, x = v ⊗ₜ[K] e := by
  classical
  let b := Basis.ofVectorSpace K V
  obtain ⟨z, hz⟩ := h2
  have hc : ∀ i, ∃ c : K, c • e = equivFinsuppOfBasisLeft b x i := fun i =>
    fund _ (by rw [← coord_lTensor, h1]) (by
      rw [← coord_lTensor, ← hz, coord_lTensor]; exact Submodule.coe_mem _)
  choose c hc using hc
  let c' := Finsupp.onFinset (equivFinsuppOfBasisLeft b x).support c (fun i hi => by
    rw [Finsupp.mem_support_iff, ← hc]; exact smul_ne_zero hi he)
  refine ⟨b.repr.symm c', ?_, ?_⟩
  · apply (equivFinsuppOfBasisLeft b).injective
    ext i
    rw [equivFinsuppOfBasisLeft_apply_tmul_apply, LinearEquiv.apply_symm_apply, ← hc]
    rfl
  · intro v hv
    rw [LinearEquiv.eq_symm_apply]
    ext i
    have h := hc i
    rw [hv, equivFinsuppOfBasisLeft_apply_tmul_apply] at h
    exact (smul_left_injective K he h).symm

theorem UpperTheory.V.Loc.lineInv :
    ∀ {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (x : V ⊗[ℚ_[l]] Bcr l), LinearMap.lTensor V (PP l).φB.toLinearMap x = x → LinearMap.lTensor V (PP l).ιB.toLinearMap x ∈ FilT A V 0 → ∃! v : V, x = v ⊗ₜ[ℚ_[l]] (1 : Bcr l) := by
  intro l _ A _ _ V _ _ _ _ x h1 h2
  refine line_abs (PP l).φB.toLinearMap (PP l).ιB.toLinearMap
    ((((PP l).PD (botExt l)).Fil 0).restrictScalars ℚ_[l]) 1 ?_ ?_ x h1 ?_
  · intro h
    apply ((PP l).PD (botExt l)).not_mem_filtration_two
    rw [← mul_one ((PP l).PD (botExt l)).t, h, mul_zero, map_zero]
    exact Submodule.zero_mem _
  · intro y hy hF
    obtain ⟨c, hc⟩ := ((PP l).PD (botExt l)).fund y (by rw [(PP l).PD_φ]; exact hy)
      (by rw [(PP l).PD_ι]; exact hF)
    exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩
  · obtain ⟨z, hz⟩ := h2
    exact ⟨z, hz⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem open_fix {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) (hH : IsOpen (H : Set (GQ v))) :
    (IntermediateField.fixedField H).fixingSubgroup = H :=
  _root_.UpperTheory.Reformulated.B.Qi42.open_fix H hH

private theorem open_index {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) (hH : IsOpen (H : Set (GQ v))) :
    H.index = finrank ℚ_[v] ↥(IntermediateField.fixedField H) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, open_fix H hH]

private theorem open_fin {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) (hH : IsOpen (H : Set (GQ v))) :
    FiniteDimensional ℚ_[v] ↥(IntermediateField.fixedField H) := by
  rw [← InfiniteGalois.isOpen_iff_finite, open_fix H hH]
  exact hH

private theorem fixed_sup {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) :
    IntermediateField.fixedField (H ⊔ Iq v) = IntermediateField.fixedField H ⊓ MaximalUnramifiedExtension v := by
  have h1 : IntermediateField.fixedField (Iq v) = MaximalUnramifiedExtension v := InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension v)
  rw [← h1]
  apply le_antisymm
  · exact le_inf (IntermediateField.fixedField_le le_sup_left) (IntermediateField.fixedField_le le_sup_right)
  · rw [IntermediateField.le_iff_le]
    refine sup_le ?_ ?_
    · rw [← IntermediateField.le_iff_le]; exact inf_le_left
    · rw [← IntermediateField.le_iff_le]; exact inf_le_right

theorem UpperTheory.V.Loc.openField :
    ∀ {v : ℕ} [Fact v.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v) (hφ : IsOpenEmbedding φ), ∃ (K : FinExt v) (e : G ≃* ↥(GK K)), Continuous e ∧ Continuous e.symm ∧ (GK K).subtype.comp e.toMonoidHom = φ ∧ φ.range = GK K ∧ φ.range.index = finrank ℚ_[v] ↥K.1 ∧ (φ.range ⊔ Iq v).index = finrank ℚ_[v] ↥(K0 K) := by
  intro v _ G _ _ _ φ hφ
  have hH : IsOpen (φ.range : Set (GQ v)) := by
    rw [MonoidHom.coe_range]; exact hφ.isOpen_range
  let K : FinExt v := ⟨IntermediateField.fixedField φ.range, open_fin _ hH⟩
  have hK : φ.range = GK K := (open_fix _ hH).symm
  let e : G ≃* ↥(GK K) := (MonoidHom.ofInjective hφ.injective).trans (MulEquiv.subgroupCongr hK)
  have he : ∀ g, ((e g : ↥(GK K)) : GQ v) = φ g := fun g => rfl
  refine ⟨K, e, ?_, ?_, ?_, hK, open_index _ hH, ?_⟩
  · exact continuous_induced_rng.2 hφ.continuous
  · rw [hφ.isInducing.continuous_iff]
    have : φ ∘ e.symm = Subtype.val := by
      funext x
      rw [Function.comp_apply, ← he, MulEquiv.apply_symm_apply]
    rw [this]
    exact continuous_subtype_val
  · ext1 g
    exact he g
  · rw [open_index _ (Subgroup.isOpen_mono le_sup_left hH), fixed_sup]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TiltFrobeniusActionPowAndInertiaTrivialOfPowEqSe
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

namespace UpperTheory.V.Loc

variable {l : ℕ} [hl : Fact l.Prime]

open scoped Formalism.Per in
private theorem tf_lift (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y) :
    ∃ (z : OC l) (x : Om l), (z : ℂ_[l]) = (x : ℂ_[l]) ∧ x ^ l ^ m = x ∧
      PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  have hz : y.untilt ^ l ^ m = y.untilt := by rw [← map_pow, hy]
  have hz' : ((y.untilt : OC l) : ℂ_[l]) ^ l ^ m = (y.untilt : OC l) := by
    have := congrArg (fun t : OC l => (t : ℂ_[l])) hz
    simpa using this
  have hint : IsIntegral (Om l) ((y.untilt : OC l) : ℂ_[l]) := by
    refine ⟨X ^ l ^ m - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1), ?_⟩
    simp [hz']
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one (Om l) _
    (IsAlgClosed.degree_eq_one_of_irreducible (Om l) (minpoly.irreducible hint))
  refine ⟨y.untilt, x, hx.symm, ?_, (PreTilt.mk_untilt_eq_coeff_zero y).symm⟩
  apply (algebraMap (Om l) ℂ_[l]).injective
  have hx' : algebraMap (Om l) ℂ_[l] x = (y.untilt : OC l) := hx
  rw [map_pow, hx', hz']

private theorem tf_act {P : LocPrime l} (AI : LocAinf l P) (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y)
    {z : OC l} {x : Om l} (hzx : (z : ℂ_[l]) = (x : ℂ_[l]))
    (h0 : PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z)
    (g : GQ l) (k : ℕ) (hg : g x = x ^ k) : AI.actT g y = y ^ k := by
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g y 0 _ h0
  rw [hzx, AI.actC_ext, hg, PadicComplex.coe_eq, map_pow, ← PadicComplex.coe_eq, ← hzx] at h1
  have h3 : y' = z ^ k := Subtype.ext (by rw [h1]; simp)
  refine GlobalTheory.UnramifiedCrys.eq_of_coeff_zero hm (by rw [← map_pow, hy])
    (by rw [← pow_mul, mul_comm, pow_mul, hy]) ?_
  rw [h2, map_pow, h0, h3]
  exact map_pow _ _ _

private theorem tf_root {x : Om l} {m : ℕ} (hm : 0 < m) (hx : x ^ l ^ m = x) (h0 : x ≠ 0) :
    ∃ n, 0 < n ∧ ¬ l ∣ n ∧ x ^ n = 1 := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  refine ⟨l ^ m - 1, by omega, fun h => ?_, ?_⟩
  · have h2 := (Nat.dvd_sub_iff_right h1.le (dvd_pow_self l hm.ne')).mp h
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h2)
  · apply mul_right_cancel₀ h0
    rw [← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]

end UpperTheory.V.Loc

theorem UpperTheory.tilt_frobenius_action_pow_and_inertia_trivial_of_pow_eq_self :
    ∀ {l : ℕ} [Fact l.Prime] (y : OCb l) (m : ℕ), 0 < m → y ^ l ^ m = y → (∀ σ : GQ l, IsFrob σ → (AIP l).actT σ y = y ^ l) ∧ ∀ g ∈ Iq l, (AIP l).actT g y = y := by
  intro l hl y m hm hy
  obtain ⟨z, x, hzx, hx, h0⟩ := tf_lift y hm hy
  refine ⟨fun σ hσ => tf_act _ y hm hy hzx h0 σ l ?_, fun g hg => ?_⟩
  · by_cases hx0 : x = 0
    · rw [hx0, map_zero, zero_pow hl.out.ne_zero]
    obtain ⟨n, hn0, hn, hxn⟩ := tf_root hm hx hx0
    have hnorm : ‖x‖ = 1 := by
      have h1 : ‖x‖ ^ n = 1 := by rw [← norm_pow, hxn, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn0.ne').mp h1
    exact KStar.IdealValuations.norm_aut_and_roots.2 n _ _ hn (by rw [← map_pow, hxn, map_one])
      (by rw [← pow_mul, mul_comm, pow_mul, hxn, one_pow]) (hσ x hnorm.le)
  · refine (tf_act _ y hm hy hzx h0 g 1 ?_).trans (pow_one y)
    rw [pow_one]
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]
    rw [Iq, IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg x (IntermediateField.subset_adjoin _ _ (tf_root hm hx hx0))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fDescAvg
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem z1fDesc_avg {k G W : Type} [Field k] [CharZero k] [Group G] [AddCommGroup W] [Module k W]
    (a : G → W →ₗ[k] W) (hmul : ∀ g h w, a (g * h) w = a g (a h w)) (f : G → W)
    (hf : ∀ g h, f (g * h) = f g + a g (f h)) (H : Subgroup G) [H.FiniteIndex] (x : W)
    (hx : ∀ h ∈ H, f h = a h x - x) : ∃ y, ∀ g, f g = a g y - y := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set f' : G → W := fun g => f g - (a g x - x) with hf'
  have hc : ∀ g h, f' (g * h) = f' g + a g (f' h) := by
    intro g h
    simp only [hf', hf, hmul, map_sub]
    abel
  have hH : ∀ g h, h ∈ H → f' (g * h) = f' g := by
    intro g h hh
    rw [hc]
    have : f' h = 0 := by simp only [hf', hx h hh, sub_self]
    rw [this, map_zero, add_zero]
  let F : G ⧸ H → W := Quotient.lift f' (by
    intro g g' hgg
    have h1 : g⁻¹ * g' ∈ H := QuotientGroup.leftRel_apply.1 hgg
    have := hH g _ h1
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hF : ∀ (g : G) (q : G ⧸ H), F (g • q) = f' g + a g (F q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H z => exact hc g z
  set S : W := ∑ q, F q with hS
  have hsum : ∀ g, S = (Fintype.card (G ⧸ H) : k) • f' g + a g S := by
    intro g
    have e1 : ∑ q, F (g • q) = S := Equiv.sum_comp (MulAction.toPerm g) F
    refine e1.symm.trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum,
      Nat.cast_smul_eq_nsmul, ← hS]
  have hn : (Fintype.card (G ⧸ H) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨x - (Fintype.card (G ⧸ H) : k)⁻¹ • S, fun g => ?_⟩
  have e : f' g = (Fintype.card (G ⧸ H) : k)⁻¹ • (S - a g S) := by
    rw [eq_inv_smul_iff₀ hn, eq_sub_iff_add_eq]
    exact (hsum g).symm
  have e2 : f g = f' g + (a g x - x) := by simp only [hf', sub_add_cancel]
  rw [e2, e, map_sub, map_smul, smul_sub]
  abel

theorem UpperTheory.V.Loc.z1fDesc :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V) (H : Subgroup G) [H.Normal] [H.FiniteIndex], ∀ c ∈ Z1 ρ, (c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ ↔ (fun h : H => c h) ∈ UpperTheory.V.Loc.finiteCocycles (φ.comp H.subtype) (ρ.comp H.subtype : Representation A H V)) := by
  intro l _ G _ _ _ φ A _ _ V _ _ _ _ _ _ _ _ _ ρ H _ _ c hc
  constructor
  · rintro ⟨-, x, hx⟩
    exact ⟨⟨hc.1.comp continuous_subtype_val, fun g h => hc.2 g h⟩, x, fun h => hx h⟩
  · rintro ⟨-, x, hx⟩
    refine ⟨hc, ?_⟩
    refine z1fDesc_avg (k := ℚ_[l]) (fun g => (actC φ ρ g).restrictScalars ℚ_[l]) ?_
      (fun g => c g ⊗ₜ[ℚ_[l]] (1 : Bcr l)) ?_ H x (fun h hh => hx ⟨h, hh⟩)
    · intro g h w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [actC]
      | add u v hu hv => simp only [map_add (f := _), hu, hv]
    · intro g h
      simp [actC, hc.2 g h, add_tmul]
end

