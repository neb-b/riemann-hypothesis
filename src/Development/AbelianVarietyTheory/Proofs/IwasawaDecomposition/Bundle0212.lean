module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
public import Formalism.LocalToGlobal.Divisibility.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroup
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


open Classical in
def twist (τ : E →+* ℂ) : ℂ →+* ℂ :=
  if (InfinitePlace.mk τ).embedding = τ then RingHom.id ℂ else starRingEnd ℂ

theorem twist_twist (τ : E →+* ℂ) (z : ℂ) : twist τ (twist τ z) = z := by
  unfold twist; split_ifs <;> simp

theorem twist_star (τ : E →+* ℂ) (z : ℂ) : twist τ (star z) = star (twist τ z) := by
  unfold twist; split_ifs <;> simp

theorem continuous_twist (τ : E →+* ℂ) : Continuous (twist τ) := by
  unfold twist; split_ifs
  · exact continuous_id
  · exact Complex.continuous_conj

theorem twist_embedding (w : InfinitePlace E) : twist w.embedding = RingHom.id ℂ := by
  unfold twist; rw [if_pos (by rw [InfinitePlace.mk_embedding])]

theorem coord_eq (τ : E →+* ℂ) (z : Cinf E) : coord τ z = twist τ (z (InfinitePlace.mk τ)) := by
  unfold coord twist; split_ifs <;> rfl

open Classical in
theorem atEmb_apply (τ : E →+* ℂ) (z : ℂ) (w : InfinitePlace E) :
    atEmb τ z w = if w = InfinitePlace.mk τ then twist τ z else 0 := by
  unfold atEmb twist
  rw [Pi.single_apply]
  split_ifs <;> simp_all

def sN (τ : E →+* ℂ) : ℂ →ₙ+* Cinf E where
  toFun := atEmb τ
  map_mul' z z' := (atEmb_mul τ z z').symm
  map_zero' := funext fun w => by classical simp [atEmb_apply]
  map_add' z z' := funext fun w => by
    classical
    simp only [atEmb_apply, Pi.add_apply]
    split_ifs <;> simp

theorem sN_apply (τ : E →+* ℂ) (z : ℂ) : sN τ z = atEmb τ z := rfl

theorem continuous_sN (τ : E →+* ℂ) : Continuous (sN τ) := by
  classical
  refine continuous_pi fun w => ?_
  simp only [sN_apply, atEmb_apply]
  split_ifs
  · exact continuous_twist τ
  · exact continuous_const

def yG (τ : E →+* ℂ) : GL (Fin n) ℂ →* GL (Fin n) (Cinf E) := cornerGL n (sN τ)

open Classical in
theorem yG_apply (τ : E →+* ℂ) (g : GL (Fin n) ℂ) (i j : Fin n) (w : InfinitePlace E) :
    (yG τ g).val i j w =
      if w = InfinitePlace.mk τ then twist τ (g.val i j) else (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  change (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j w - sN τ ((1 : Matrix (Fin n) (Fin n) ℂ) i j) w +
    sN τ (g.val i j) w = _
  simp only [sN_apply, atEmb_apply, Matrix.one_apply]
  split_ifs <;> simp_all

end GlobalTheory.EmbUnitary

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cEmb_mem (τ : E →+* ℂ) (x : UA E n) : (cEmb τ x).val ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hx : Formalism.UG.cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
  have h1 := congrArg (RingHom.mapMatrix ((coord τ).comp (pInf E))) hx
  rw [mul_one, map_mul, map_one] at h1
  rw [Matrix.mem_unitaryGroup_iff', ← h1]
  congr 1
  ext i j
  exact (GlobalTheory.DefiniteBC.coord_conjAd τ _).symm

theorem cEmb_infGL (τ' : E →+* ℂ) (y : GL (Fin n) (Cinf E)) (h : infGL E n y ∈ UA E n) (i j : Fin n) :
    (cEmb τ' ⟨_, h⟩).val i j = coord τ' (y.val i j) := by
  have e : cEmb τ' ⟨_, h⟩ = GeneralLinearGroup.map (coord τ') y := by
    change GeneralLinearGroup.map (coord τ') (GeneralLinearGroup.map (pInf E) (infGL E n y)) = _
    rw [pInf_infGL]
  rw [e]
  rfl

theorem yG_unitary (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) :
    (yG τ (GlobalTheory.Branching.unitaryIncl n u)).valᴴ * (yG τ (GlobalTheory.Branching.unitaryIncl n u)).val = 1 := by
  classical
  have hu : star (u : Matrix (Fin n) (Fin n) ℂ) * u = 1 := Matrix.mem_unitaryGroup_iff'.1 u.2
  refine Matrix.ext fun i j => funext fun w => ?_
  simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply, yG_apply]
  split_ifs with hw
  · have h2 := congrFun₂ hu i j
    simp only [Matrix.mul_apply, Matrix.star_apply] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← twist_star, ← map_mul, ← map_sum]
    change twist τ (∑ k, star ((u : Matrix (Fin n) (Fin n) ℂ) k i) * (u : Matrix (Fin n) (Fin n) ℂ) k j) = _
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · by_cases h : i = j
    · subst h; simp [Matrix.one_apply]
    · simp [Matrix.one_apply, h, Ne.symm h]

end GlobalTheory.EmbUnitary

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem infGL_yG_mem_UA (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) :
    infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n u)) ∈ UA E n :=
  infGL_mem_UA _ (yG_unitary τ u)

theorem twist_one_apply (τ : E →+* ℂ) (i j : Fin n) :
    twist τ ((1 : Matrix (Fin n) (Fin n) ℂ) i j) = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem mem_embU (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) :
    (⟨_, infGL_yG_mem_UA τ u⟩ : UA E n) ∈ embU n τ := by
  classical
  refine ⟨pFin_infGL _, ?_⟩
  refine Subgroup.mem_iInf.2 fun τ' => Subgroup.mem_iInf.2 fun h => MonoidHom.mem_ker.2 ?_
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [cEmb_infGL, coord_eq, yG_apply, if_neg h, twist_one_apply]
  rfl

def inv (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) : embU n τ :=
  ⟨⟨_, infGL_yG_mem_UA τ u⟩, mem_embU τ u⟩

def fwd (τ : E →+* ℂ) (x : embU n τ) : Matrix.unitaryGroup (Fin n) ℂ := ⟨(cEmb τ x.1).val, cEmb_mem τ x.1⟩

theorem fwd_inv (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) : fwd τ (inv τ u) = u := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  change (cEmb τ ⟨_, infGL_yG_mem_UA τ u⟩).val i j = _
  rw [cEmb_infGL, coord_eq, yG_apply, if_pos rfl, twist_twist]
  rfl

theorem inv_fwd (τ : E →+* ℂ) (x : embU n τ) : inv τ (fwd τ x) = x := by
  classical
  have hx := Subgroup.mem_inf.1 x.2
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · change GeneralLinearGroup.map (pInf E) (infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n (fwd τ x)))) = _
    rw [pInf_infGL]
    refine Units.ext (Matrix.ext fun i j => funext fun w => ?_)
    rw [yG_apply]
    split_ifs with hw
    · subst hw
      change twist τ (coord τ (pInf E (x.1.1.val i j))) = _
      rw [coord_eq, twist_twist]
      rfl
    · have h1 : InfinitePlace.mk w.embedding ≠ InfinitePlace.mk τ := by
        rw [InfinitePlace.mk_embedding]; exact hw
      have hk := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 w.embedding) h1)
      have h2 := congrArg (fun g : GL (Fin n) ℂ => g.val i j) hk
      change coord w.embedding (pInf E (x.1.1.val i j)) = _ at h2
      rw [coord_eq, twist_embedding, InfinitePlace.mk_embedding] at h2
      exact h2.symm
  · change GeneralLinearGroup.map (pFin E) (infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n (fwd τ x)))) = _
    rw [pFin_infGL]
    exact (MonoidHom.mem_ker.1 hx.1).symm

end GlobalTheory.EmbUnitary

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_coord (τ : E →+* ℂ) : Continuous (coord τ) := by
  have : (coord τ : Cinf E → ℂ) = fun z => twist τ (z (InfinitePlace.mk τ)) := funext (coord_eq τ)
  rw [this]
  exact (continuous_twist τ).comp (continuous_apply _)

theorem continuous_fwd (τ : E →+* ℂ) : Continuous (fwd τ : embU n τ → Matrix.unitaryGroup (Fin n) ℂ) := by
  refine Continuous.subtype_mk ?_ _
  change Continuous fun x : embU n τ => (x.1.1.val).map (fun a => coord τ (pInf E a))
  exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_map
    ((continuous_coord τ).comp continuous_pInf')

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

def phi (τ : E →+* ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) (Ad E) :=
  corner (matN n (sInf E)) (corner (matN n (sN τ)) M)

theorem continuous_phi (τ : E →+* ℂ) : Continuous (phi (n := n) τ) := by
  change Continuous fun M : Matrix (Fin n) (Fin n) ℂ => 1 - matN n (sInf E) 1 +
    (1 - matN n (sN τ) 1 + M.map (sN τ)).map (sInf E)
  exact continuous_const.add ((continuous_const.add (continuous_id.matrix_map (continuous_sN τ))).matrix_map
    continuous_sInf)

theorem continuous_inv (τ : E →+* ℂ) : Continuous (inv τ : Matrix.unitaryGroup (Fin n) ℂ → embU n τ) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ => phi τ (u : Matrix (Fin n) (Fin n) ℂ)
    exact (continuous_phi τ).comp continuous_subtype_val
  · have e : ∀ u : Matrix.unitaryGroup (Fin n) ℂ,
        ((infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n u)))⁻¹ : GL (Fin n) (Ad E)).val =
          phi τ (star (u : Matrix (Fin n) (Fin n) ℂ)) := fun u => by
      rw [← map_inv, ← map_inv]
      rfl
    change Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ =>
      ((infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n u)))⁻¹ : GL (Fin n) (Ad E)).val
    simp only [e]
    exact (continuous_phi τ).comp (continuous_star.comp continuous_subtype_val)

def equiv (τ : E →+* ℂ) : embU n τ ≃ₜ* Matrix.unitaryGroup (Fin n) ℂ where
  toFun := fwd τ
  invFun := inv τ
  left_inv := inv_fwd τ
  right_inv := fwd_inv τ
  map_mul' x y := Subtype.ext (by
    change (cEmb τ (x.1 * y.1)).val = (cEmb τ x.1).val * (cEmb τ y.1).val
    rw [map_mul]
    rfl)
  continuous_toFun := continuous_fwd τ
  continuous_invFun := continuous_inv τ

theorem exists_equiv_unitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ),
    ∃ e : embU n τ ≃ₜ* Matrix.unitaryGroup (Fin n) ℂ, ∀ x : embU n τ,
      GlobalTheory.Branching.unitaryIncl n (e x) = cEmb τ (x : UA E n) := by
  intro E _ _ _ n τ
  exact ⟨equiv τ, fun x => Units.ext rfl⟩

end GlobalTheory.EmbUnitary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteUnitaryArchimedeanPointsDistinctPlaces
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem UA_ext_cEmb {a b : UA E n}
    (hfin : GeneralLinearGroup.map (pFin E) a.1 = GeneralLinearGroup.map (pFin E) b.1)
    (hinf : ∀ τ : E →+* ℂ, cEmb τ a = cEmb τ b) : a = b := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply Prod.ext
  · have key : pInf E (a.1.1 i j) = pInf E (b.1.1 i j) := by
      funext w
      have h := congrArg (fun g : GL (Fin n) ℂ => g.1 i j) (hinf w.embedding)
      simp only [cEmb, cInf, MonoidHom.comp_apply, GeneralLinearGroup.map, Subgroup.coe_subtype] at h
      change coord w.embedding (pInf E (a.1.1 i j)) = coord w.embedding (pInf E (b.1.1 i j)) at h
      have hw : InfinitePlace.mk w.embedding = w := InfinitePlace.mk_embedding w
      unfold coord at h
      rw [if_pos (by rw [hw])] at h
      simpa [hw] using h
    exact (infEq E).symm.injective key
  · have h := congrArg (fun g : GL (Fin n) (Af E) => g.1 i j) hfin
    exact h

theorem embU_commute (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ τ' : E →+* ℂ)
    (hne : InfinitePlace.mk τ ≠ InfinitePlace.mk τ') : ∀ x ∈ embU n τ, ∀ y ∈ embU n τ', Commute x y := by
  intro x hx y hy
  simp only [embU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hx hy
  obtain ⟨hxf, hxi⟩ := hx
  obtain ⟨hyf, hyi⟩ := hy
  rw [infU, MonoidHom.mem_ker] at hxf hyf
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hxf hyf
  apply UA_ext_cEmb
  · simp only [Subgroup.coe_mul, map_mul, hxf, hyf]
  · intro σ
    simp only [map_mul]
    by_cases h : InfinitePlace.mk σ = InfinitePlace.mk τ
    · have : InfinitePlace.mk σ ≠ InfinitePlace.mk τ' := h ▸ hne
      rw [hyi σ this, one_mul, mul_one]
    · rw [hxi σ h, one_mul, mul_one]

end GlobalTheory.UnitaryBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommutingEndAlgebrasCommonFixedVector
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory

open NumberField IsDedekindDomain Matrix in
private theorem sum_smulRight_finBasis_mul_smulRight_eq_one {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (w : W) (ℓ : Module.Dual ℂ W) (h : ℓ w = 1) :
    ∑ i, ℓ.smulRight (Module.finBasis ℂ W i) * ((Module.finBasis ℂ W).coord i).smulRight w = 1 := by
  ext x
  simpa [h] using (Module.finBasis ℂ W).sum_repr x

open NumberField IsDedekindDomain Matrix in
private theorem exists_dual_algHom_smulRight_apply_ne_zero {W V : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [AddCommGroup V] [Module ℂ V] (w : W) (ℓ : Module.Dual ℂ W)
    (h : ℓ w = 1) (Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V) {y : V} (hy : y ≠ 0) :
    ∃ φ : Module.Dual ℂ W, Φ (φ.smulRight w) y ≠ 0 := by
  by_contra! hzero
  apply hy
  calc y = Φ 1 y := by simp
    _ = ∑ i, Φ (ℓ.smulRight (Module.finBasis ℂ W i))
          (Φ (((Module.finBasis ℂ W).coord i).smulRight w) y) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← sum_smulRight_finBasis_mul_smulRight_eq_one w ℓ h, map_sum, LinearMap.sum_apply]
        simp only [map_mul, Module.End.mul_apply]
    _ = 0 := by simp [hzero]

open NumberField IsDedekindDomain Matrix in
private theorem smulRight_mul_smulRight_of_apply_eq_one {W : Type} [AddCommGroup W] [Module ℂ W]
    (w : W) (ℓ φ : Module.Dual ℂ W) (h : ℓ w = 1) :
    ℓ.smulRight w * φ.smulRight w = φ.smulRight w := by
  ext x
  simp [h]


open NumberField IsDedekindDomain Matrix in
theorem _root_.GlobalTheory.commuting_endAlgebras_common_fixed_vector :
    ∀ (ι : Type) [Fintype ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)]
      [∀ v, FiniteDimensional ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V]
      (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v)
      (ℓ : ∀ v, Module.Dual ℂ (Wv v)), Nontrivial V → (∀ v, ℓ v (w v) = 1) →
      (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) →
      ∃ y : V, y ≠ 0 ∧ ∀ v, Φ v ((ℓ v).smulRight (w v)) y = y := by
  intro ι _ Wv _ _ _ V _ _ Φ w ℓ _ hℓ hcomm
  classical
  have key : ∀ s : Finset ι, ∃ y : V, y ≠ 0 ∧ ∀ v ∈ s, Φ v ((ℓ v).smulRight (w v)) y = y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨y, hy⟩ := exists_ne (0 : V)
      exact ⟨y, hy, by simp⟩
    | insert v s hv ih =>
      obtain ⟨y, hy0, hy⟩ := ih
      obtain ⟨φ, hφ⟩ := exists_dual_algHom_smulRight_apply_ne_zero (w v) (ℓ v) (hℓ v) (Φ v) hy0
      refine ⟨Φ v (φ.smulRight (w v)) y, hφ, fun u hu => ?_⟩
      rcases Finset.mem_insert.mp hu with rfl | hu
      · rw [← Module.End.mul_apply, ← map_mul,
          smulRight_mul_smulRight_of_apply_eq_one _ _ _ (hℓ u)]
      · have huv : u ≠ v := fun h => hv (h ▸ hu)
        rw [← Module.End.mul_apply, (hcomm u v huv _ _).eq, Module.End.mul_apply, hy u hu]
  obtain ⟨y, hy0, hy⟩ := key Finset.univ
  exact ⟨y, hy0, fun v => hy v (Finset.mem_univ v)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CxFactsOfPrims
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
open Formalism.IndefR.CxPass
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem cxFacts_of_prims : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → CxFacts (R.toCx3 F) F.cr (F.eV (R.toCx3 F).zs) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F n hOk hSep hC hP
  let X := R.toCx3 F
  have hKR : X.KFormR := RealDat3.kFormR_of (F := F) hC.base.models
  have hKL : X.KFormL := RealDat3.kFormL_of (F := F) hC.base.models
  have hJR : X.JIsoR F.cv := RealDat3.jIsoR_of (F := F) hC.base.models
  have hJL : X.JIsoL F.cv := RealDat3.jIsoL_of (F := F) hC.base.models
  have hStable : X.zs.Stable :=
    CxData.cutStable X hKR hKL
      (definite_kernel_stable hKR hP.gEquiv.1 hP.hecke.1.choose_spec)
      (lift_kernel_stable hKL hP.gEquiv.2 hP.hecke.2.choose_spec)
      (definite_adjoint_closed hOk hP.heckeR hKR hJR)
      (lift_adjoint_closed hOk hP.heckeL hKL hJL)
  have hWF : (F.fc X.zs).Df1.WF :=
    A3.side_well_formed hOk F.P1 F.ψ1 X.zs hStable hP.block hSep
  have hPos : X.H4pos := ⟨fun _ => hP.posScal.1, hP.posScal.2, RealDat.nP_pos⟩
  have hRatZ : X.RatZ :=
    Formalism.IndefR.Rat.ratZOfTests X F.cv hKR hKL hJR hJL hP.rowTest hP.liftTest
  have hRat : X.RatLev F.cr F.cv true :=
    rationality_at_level_of_equivariance hOk hKR hJR hRatZ hP.gUnit.1 hP.gEquiv.1 true
  have hDn : X.DnLev F.cv true :=
    descent_of_types hOk hKR hJR hRatZ hP.gUnit.1 hP.gEquiv.1 hP.h2P hP.levE.1 hP.levE.2 true
  have hUp : X.UpLev F.cv true :=
    upper_level_of_types hOk hKR hJR hP.gUnit.1 hP.gEquiv.1 hP.levE.1 hP.levE.2 true
  have hGood : X.CoordinatesInGoodPart F.cr F.cv true := definite_coordinates_in_good_part X true
  have hIso : X.IsoR F.cr true := definite_isometry_of_norms hOk hJR ⟨rfl, rfl⟩ true
  have hSubspaces : X.CrdZ F.cr true := definite_coordinates_in_subspaces X true
  have hRows : X.H2 F.cr true ∧ X.H4 F.cr true :=
    cutRows (X := X) F.cr F.cv true hWF hPos hIso hSubspaces hGood hRat hDn hUp
      (RealDat3.thmBop_of (F := F) hP.thmB true) (hP.sumE true)
  exact
    { wf := hWF
      h2 := hRows.1
      pos := hPos
      theta := X.theta_eV F.cr F.cv (F.eV X.zs) hJR hRat hDn hUp hGood (EvTie.evTie_of_ok hOk F X) _ }

end GlobalTheory.Mem.SJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversal
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.CoefIrred

theorem vv_universal :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : Type) [AddCommGroup V] [Module ℂ V]
      (F : (∀ v, nablaSq ℂ n (lam v)) →ₘₗ[ℂ] V),
      ∃! f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] V, ∀ u, f (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) = F u := by
  intro ι _ n lam V _ _ F
  have hB : ∀ i, Formalism.L2.DIV.bVV ℂ lam i = tenMul lam (fun τ => ssBasis ℂ (lam τ) (i τ)) := by
    intro i
    apply Subtype.ext
    rw [Formalism.L2.DIV.bVV_coe, tenMul_coe, Formalism.L2.DIV.bVVfun]
    simp only [ssBasis_coe]
  refine ⟨(Formalism.L2.DIV.bVV ℂ lam).constr ℂ (fun i => F (fun τ => ssBasis ℂ (lam τ) (i τ))), ?_, ?_⟩
  · intro u
    have := Module.Basis.ext_multilinear (f := ((Formalism.L2.DIV.bVV ℂ lam).constr ℂ
      (fun i => F (fun τ => ssBasis ℂ (lam τ) (i τ)))).compMultilinearMap (tenMul lam)) (g := F)
      (fun τ => ssBasis ℂ (lam τ)) (fun v => by
        simp only [LinearMap.compMultilinearMap_apply, ← hB, Module.Basis.constr_basis])
    exact congrArg (fun m => m u) this
  · intro g hg
    apply (Formalism.L2.DIV.bVV ℂ lam).ext
    intro i
    rw [Module.Basis.constr_basis, hB, hg]

end GlobalTheory.CoefIrred
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvInjOfTieIn
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemberEvalInj

theorem evInj_of_tieIn : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → EvInj T R v₀ :=
  fun _ _ _ _ _ _ _ T _ R _ v₀ _ hm ht _ => GlobalTheory.EvalAtUnitVector.evInj T R v₀ hm.HW ht.hv₀

end GlobalTheory.MemberEvalInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnHighestWeightPolynomialMapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_column_highest_weight_polynomial_map : ∀ (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (U : Submodule ℂ (X →ₗ[ℂ] Pol ι m n)), U ≠ ⊥ → (∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) → ∃ Φ ∈ U, Φ ≠ 0 ∧ (∀ τ k l, k < l → colLie m τ k l ∘ₗ Φ = 0) ∧ ∃ μ : ι → Fin n → ℤ, ∀ τ k, colLie m τ k k ∘ₗ Φ = (μ τ k : ℂ) • Φ := by
  first | exact @GlobalTheory.DefLift.exists_colHighest | exact GlobalTheory.DefLift.exists_colHighest | (intros; apply GlobalTheory.DefLift.exists_colHighest <;> assumption)
end

