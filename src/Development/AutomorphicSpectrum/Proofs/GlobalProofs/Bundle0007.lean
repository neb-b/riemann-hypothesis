module

public import Mathlib
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.FormalDegreeBessel.StatementG
public import ReciprocityTheory.Hypotheses.GalCoh
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
public import GroundTheory.ProfiniteCohomology.ContinuousCochains
public import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixing

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsOrthogonalHermitianSubspace
section
open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.JStable


open Module in
theorem exists_adapted_onb {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Submodule ℂ (EuclideanSpace ℂ ι)) :
    ∃ (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (T : Set ι),
      W = Submodule.span ℂ (b '' T) := by
  classical
  let v : Set (EuclideanSpace ℂ ι) := Set.range (fun i => ((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ ι))
  have hon : Orthonormal ℂ (fun i => ((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ ι)) :=
    (stdOrthonormalBasis ℂ W).orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hv : Orthonormal ℂ ((↑) : v → EuclideanSpace ℂ ι) :=
    (orthonormal_subtype_range hon.linearIndependent.injective).2 hon
  obtain ⟨u, bu, hvu, hbu⟩ := hv.exists_orthonormalBasis_extension
  have hcard : Fintype.card u = Fintype.card ι :=
    (Module.finrank_eq_card_basis bu.toBasis).symm.trans finrank_euclideanSpace
  let e : u ≃ ι := Fintype.equivOfCardEq hcard
  refine ⟨bu.reindex e, e '' {x | (x : EuclideanSpace ℂ ι) ∈ v}, ?_⟩
  have himg : (bu.reindex e) '' (e '' {x | (x : EuclideanSpace ℂ ι) ∈ v}) = v := by
    rw [Set.image_image]
    ext y
    simp only [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hbu, Set.mem_image,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hvu hy⟩, hy, rfl⟩
  rw [himg]
  have hr : W.subtype '' Set.range (stdOrthonormalBasis ℂ W) = v := (Set.range_comp _ _).symm
  rw [← hr, Submodule.span_image, ← (stdOrthonormalBasis ℂ W).coe_toBasis,
    (stdOrthonormalBasis ℂ W).toBasis.span_eq, Submodule.map_subtype_top]

variable {n : ℕ} (ε : Fin n → Bool)

def ext0 (s : Bool) : EuclideanSpace ℂ {i : Fin n // ε i = s} →ₗ[ℂ] (Fin n → ℂ) where
  toFun x a := if h : ε a = s then x ⟨a, h⟩ else 0
  map_add' x y := by
    funext a
    by_cases h : ε a = s <;> simp [h]
  map_smul' c x := by
    funext a
    by_cases h : ε a = s <;> simp [h]

def res0 (s : Bool) (v : Fin n → ℂ) : EuclideanSpace ℂ {i : Fin n // ε i = s} :=
  WithLp.toLp 2 fun i => v i

lemma extendByZero_apply_of_ne {s : Bool} (x : EuclideanSpace ℂ {i : Fin n // ε i = s}) {a : Fin n}
    (h : ε a ≠ s) : ext0 ε s x a = 0 := by
  simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h]

lemma extendByZero_restrict_eigen_projection (s : Bool) (v : Fin n → ℂ) :
    ext0 ε s (res0 ε s v) =
      (1 / 2 : ℂ) • (v + (if s then (1 : ℂ) else -1) • (Formalism.REAL.Jm ε *ᵥ v)) := by
  funext a
  have hJ : (Formalism.REAL.Jm ε *ᵥ v) a = (if ε a then 1 else -1) * v a := by
    simp [Formalism.REAL.Jm, Matrix.mulVec_diagonal]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hJ, ext0, LinearMap.coe_mk, AddHom.coe_mk, res0]
  cases s <;> cases h : ε a <;> simp <;> ring

lemma eq_extendByZero_restrict_sum (v : Fin n → ℂ) :
    v = ext0 ε true (res0 ε true v) + ext0 ε false (res0 ε false v) := by
  funext a
  simp only [Pi.add_apply, ext0, LinearMap.coe_mk, AddHom.coe_mk, res0]
  cases h : ε a <;> simp

lemma sum_extendByZero_fin_eq_sum_of_eq (s : Bool) (x y : EuclideanSpace ℂ {i : Fin n // ε i = s}) :
    ∑ a, star (ext0 ε s x a) * ext0 ε s y a = inner ℂ x y := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a => ε a = s)
    (fun a => star (ext0 ε s x a) * ext0 ε s y a)]
  have h2 : ∑ a : {a // ¬ ε a = s}, star (ext0 ε s x a) * ext0 ε s y a = 0 :=
    Finset.sum_eq_zero (fun a _ => by rw [extendByZero_apply_of_ne ε x a.2, star_zero, zero_mul])
  rw [h2, add_zero, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hx : ∀ z : EuclideanSpace ℂ {i : Fin n // ε i = s}, ext0 ε s z i.1 = z i := by
    intro z
    simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk, dif_pos i.2]
  rw [hx x, hx y]
  simp [mul_comm]

theorem exists_KG_coordinate (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ v ∈ W, Formalism.REAL.Jm ε *ᵥ v ∈ W) :
    ∃ (k : Formalism.REAL.KG ε) (S : Set (Fin n)),
      W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map
        (Formalism.REAL.toMK k).mulVecLin := by
  classical
  choose b T hT using fun s : Bool => exists_adapted_onb (W.comap (ext0 ε s))
  have hres : ∀ (s : Bool) (v : Fin n → ℂ), v ∈ W → res0 ε s v ∈ W.comap (ext0 ε s) := by
    intro s v hv
    rw [Submodule.mem_comap, extendByZero_restrict_eigen_projection]
    exact W.smul_mem _ (W.add_mem hv (W.smul_mem _ (hW v hv)))
  have hdecomp : W = (W.comap (ext0 ε true)).map (ext0 ε true) ⊔
      (W.comap (ext0 ε false)).map (ext0 ε false) := by
    refine le_antisymm (fun v hv => ?_) (sup_le (Submodule.map_le_iff_le_comap.2 le_rfl)
      (Submodule.map_le_iff_le_comap.2 le_rfl))
    rw [eq_extendByZero_restrict_sum ε v]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem (hres true v hv))
      (Submodule.mem_map_of_mem (hres false v hv))
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) ℂ,
      ∀ i j, M i j = ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) i :=
    ⟨Matrix.of fun i j => ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) i, fun _ _ => rfl⟩
  have hcol : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}) (a : Fin n),
      M a i'.1 = ext0 ε s (b s i') a := by
    rintro s ⟨j, rfl⟩ a
    exact hM a j
  have hMM : Mᴴ * M = 1 := by
    ext j l
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    by_cases hjl : ε j = ε l
    · have h1 : ∀ a, M a j = ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) a := fun a => hcol (ε j) ⟨j, rfl⟩ a
      have h2 : ∀ a, M a l = ext0 ε (ε j) (b (ε j) ⟨l, hjl.symm⟩) a :=
        fun a => hcol (ε j) ⟨l, hjl.symm⟩ a
      simp only [h1, h2]
      rw [sum_extendByZero_fin_eq_sum_of_eq, orthonormal_iff_ite.1 (b (ε j)).orthonormal]
      simp only [Subtype.mk.injEq]
    · have hne : j ≠ l := fun h => hjl (h ▸ rfl)
      rw [if_neg hne]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      by_cases hi : ε i = ε j
      · rw [hM i l, extendByZero_apply_of_ne ε _ (fun h => hjl (hi.symm.trans h)), mul_zero]
      · rw [hM i j, extendByZero_apply_of_ne ε _ hi, star_zero, zero_mul]
  have hMM' : M * Mᴴ = 1 := mul_eq_one_comm.1 hMM
  have hJ : M * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * M := by
    have hJd : Formalism.REAL.Jm ε = Matrix.diagonal (fun a => if ε a then (1 : ℂ) else -1) := rfl
    ext i j
    rw [hJd, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : ε i = ε j
    · simp only [hi]
      ring
    · rw [hM i j, extendByZero_apply_of_ne ε _ hi]
      ring
  have hunit : M ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hMM
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨M, Mᴴ, hMM', hMM⟩
  have hUJ : u ∈ Formalism.REAL.UJ ε := by
    show Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε
    rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, hMM, Matrix.one_mul]
  let gu : Formalism.REAL.UJ ε := ⟨u, hUJ⟩
  have hK : M ∈ Formalism.REAL.Kset ε := ⟨hunit, hJ⟩
  let k : Formalism.REAL.KG ε := ⟨gu, (Formalism.REAL.mem_KG ε gu).2 hK⟩
  let S : Set (Fin n) := {j | (⟨j, rfl⟩ : {i : Fin n // ε i = ε j}) ∈ T (ε j)}
  refine ⟨k, S, ?_⟩
  change W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map
    M.mulVecLin
  have hMcol : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}),
      M *ᵥ Pi.single i'.1 1 = ext0 ε s (b s i') := by
    intro s i'
    funext a
    rw [Matrix.mulVec_single_one, Matrix.col_apply, hcol s i' a]
  have hmemS : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}), i' ∈ T s → i'.1 ∈ S := by
    rintro s ⟨j, rfl⟩ hi'
    exact hi'
  have hset : ⇑(ext0 ε true) '' (⇑(b true) '' T true) ∪ ⇑(ext0 ε false) '' (⇑(b false) '' T false) =
      Set.range (⇑M.mulVecLin ∘ fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ)) := by
    ext x
    simp only [Set.mem_union, Set.mem_image, Set.mem_range, Function.comp_apply,
      Matrix.mulVecLin_apply]
    constructor
    · rintro (⟨y, ⟨i', hi', rfl⟩, rfl⟩ | ⟨y, ⟨i', hi', rfl⟩, rfl⟩)
      · exact ⟨⟨i'.1, hmemS true i' hi'⟩, hMcol true i'⟩
      · exact ⟨⟨i'.1, hmemS false i' hi'⟩, hMcol false i'⟩
    · rintro ⟨⟨j, hj⟩, rfl⟩
      have htr : ∀ (s : Bool) (h : ε j = s), (⟨j, h⟩ : {i : Fin n // ε i = s}) ∈ T s := by
        rintro s rfl
        exact hj
      have hback : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}), i' ∈ T s →
          ∃ y, (∃ a ∈ T s, b s a = y) ∧ ext0 ε s y = M *ᵥ Pi.single i'.1 1 :=
        fun s i' hi' => ⟨b s i', ⟨i', hi', rfl⟩, (hMcol s i').symm⟩
      rcases Bool.eq_false_or_eq_true (ε j) with h | h
      · exact Or.inl (hback _ ⟨j, h⟩ (htr _ h))
      · exact Or.inr (hback _ ⟨j, h⟩ (htr _ h))
  conv_lhs => rw [hdecomp, hT true, hT false]
  rw [Submodule.map_span, Submodule.map_span, Submodule.map_span, ← Submodule.span_union, hset,
    Set.range_comp]

end GlobalTheory.CompanionTheory.JStable
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1OfFiniteCrossedHoms
section
namespace GlobalTheory.CompanionTheory.Glob

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

noncomputable def oneCochainFun {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    (A : Rep.{0} k G) (c : locallyConstantCochains A 1) : G → A.V :=
  fun g => c.1 (fun _ => g)

theorem oneCochainFun_injective {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    (A : Rep.{0} k G) : Function.Injective (oneCochainFun A) := by
  intro c c' h
  apply Subtype.ext
  funext x
  have hx : x = fun _ => x 0 := funext fun i => congrArg x (Subsingleton.elim i 0)
  rw [hx]
  exact congrFun h (x 0)

theorem oneCochainFun_isLocallyConstant {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    (A : Rep.{0} k G) (c : locallyConstantCochains A 1) :
    IsLocallyConstant (oneCochainFun A c) := by
  have hc : IsLocallyConstant (c : (Fin 1 → G) → A) := c.2
  exact hc.comp_continuous (continuous_pi fun _ => continuous_id)

theorem oneCochainFun_cocycle {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A] (c : locallyConstantCochains A 1)
    (hc : (dLocallyConstant A 1).hom c = 0) (g h : G) :
    oneCochainFun A c (g * h) = oneCochainFun A c g + A.ρ g (oneCochainFun A c h) := by
  have key : A.ρ g ((c : (Fin 1 → G) → A) (fun i => ![g, h] i.succ)) +
      ∑ j : Fin 2, (-1 : k) ^ ((j : ℕ) + 1) •
        (c : (Fin 1 → G) → A) (Fin.contractNth j (· * ·) ![g, h]) = 0 := by
    have h1 := congrFun (congrArg Subtype.val hc) ![g, h]
    rw [dLocallyConstant_hom_apply] at h1
    exact h1
  rw [Fin.sum_univ_two] at key
  have e1 : (fun i : Fin 1 => ![g, h] i.succ) = fun _ => h := funext fun i => by
    rw [Subsingleton.elim i 0]
    rfl
  have e2 : Fin.contractNth (0 : Fin 2) (· * ·) ![g, h] = fun _ => g * h := funext fun i => by
    rw [Subsingleton.elim i 0]
    rfl
  have e3 : Fin.contractNth (1 : Fin 2) (· * ·) ![g, h] = fun _ => g := funext fun i => by
    rw [Subsingleton.elim i 0]
    rfl
  have p0 : (-1 : k) ^ (((0 : Fin 2) : ℕ) + 1) = -1 := by
    show (-1 : k) ^ 1 = -1
    exact pow_one _
  have p1 : (-1 : k) ^ (((1 : Fin 2) : ℕ) + 1) = 1 := by
    show (-1 : k) ^ 2 = 1
    exact neg_one_sq
  rw [e1, e2, e3, p0, p1, neg_one_smul, one_smul] at key
  show (c : (Fin 1 → G) → A) (fun _ => g * h) =
    (c : (Fin 1 → G) → A) (fun _ => g) + A.ρ g ((c : (Fin 1 → G) → A) (fun _ => h))
  rw [← sub_eq_zero, ← neg_eq_zero, ← key]
  abel

theorem finite_cohomology_one_of_finite_cocycles :
    ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (A : Rep.{0} k G) [IsDiscreteRep A],
      {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite →
        Finite (cohomology A 1) := by
  intro k G _ _ _ _ A _ hfin
  have hd : ∀ z : (cochainsComplex A).cycles 1,
      (dLocallyConstant A 1).hom (((cochainsComplex A).iCycles 1).hom z) = 0 := by
    intro z
    have h1 : (cochainsComplex A).iCycles 1 ≫ (cochainsComplex A).d 1 (1 + 1) = 0 :=
      (cochainsComplex A).iCycles_d 1 (1 + 1)
    rw [cochainsComplex_d] at h1
    exact congrArg (fun φ => φ.hom z) h1
  have hinj : Function.Injective ((cochainsComplex A).iCycles 1).hom :=
    (ModuleCat.mono_iff_injective ((cochainsComplex A).iCycles 1)).1 inferInstance
  have hS : ∀ z : (cochainsComplex A).cycles 1,
      oneCochainFun A (((cochainsComplex A).iCycles 1).hom z) ∈
        {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)} :=
    fun z => ⟨oneCochainFun_isLocallyConstant A _, oneCochainFun_cocycle A _ (hd z)⟩
  have hFin : Finite ((cochainsComplex A).cycles 1) := by
    haveI := hfin.to_subtype
    exact Finite.of_injective (fun z => (⟨_, hS z⟩ :
        {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}))
      (fun z₁ z₂ hz => hinj (oneCochainFun_injective A (congrArg Subtype.val hz)))
  have hepi : Epi ((cochainsComplex A).homologyπ 1) := inferInstance
  have hsurj : Function.Surjective ((cochainsComplex A).homologyπ 1).hom :=
    (ModuleCat.epi_iff_surjective ((cochainsComplex A).homologyπ 1)).1 hepi
  exact Finite.of_surjective _ hsurj

end GlobalTheory.CompanionTheory.Glob
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixingStatement
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_subgroup_le_unramified_fixing : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), NS Ω S ≤ (maxUnramifiedOutside (F := F) (Ω := Ω) S).fixingSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup | exact GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup <;> assumption)
end

