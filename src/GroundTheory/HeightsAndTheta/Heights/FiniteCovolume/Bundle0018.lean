module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0005
public import GroundTheory.HeightsAndTheta.Theta.RealSignature
public import GroundTheory.HeightsAndTheta.Theta.Unimodular.IndefiniteUnitary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdaptedReduction
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

section Transport

variable {h : HermitianForm F E W}

theorem sesq_unitary_smul (g : h.unitaryGroup) (x y : W) :
    h.toSesq (g • x) (g • y) = h.toSesq x y :=
  g.2 x y

theorem unitary_smul_scalar_smul (g : h.unitaryGroup) (a : E) (x : W) : g • (a • x) = a • (g • x) :=
  map_smul (g : W ≃ₗ[E] W) a x

theorem mem_inv_smul_iff {g : h.unitaryGroup} {La : AddSubgroup W} {x : W} :
    x ∈ g⁻¹ • La ↔ g • x ∈ La := by
  change x ∈ ((g⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) • La ↔ _
  rw [AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem lineCoeffs_inv_smul (g : h.unitaryGroup) (La : AddSubgroup W) (x : W) :
    lineCoeffs (E := E) (g⁻¹ • La) x = lineCoeffs (E := E) La (g • x) := by
  ext a
  change a • x ∈ g⁻¹ • La ↔ a • (g • x) ∈ La
  rw [mem_inv_smul_iff, unitary_smul_scalar_smul]

theorem dualLattice_inv_smul (g : h.unitaryGroup) (La : AddSubgroup W) :
    dualLattice h (g⁻¹ • La) = g⁻¹ • dualLattice h La := by
  ext y
  rw [mem_inv_smul_iff]
  change (∀ x ∈ g⁻¹ • La, h.toSesq y x ∈ integralClosure ℤ E) ↔
    ∀ x ∈ La, h.toSesq (g • y) x ∈ integralClosure ℤ E
  constructor
  · intro hy x hx
    have hx' : g⁻¹ • x ∈ g⁻¹ • La := by rw [mem_inv_smul_iff, smul_inv_smul]; exact hx
    have := hy _ hx'
    rwa [← sesq_unitary_smul g, smul_inv_smul] at this
  · intro hy x hx
    rw [mem_inv_smul_iff] at hx
    rw [← sesq_unitary_smul g]
    exact hy _ hx

theorem isDIntegral_inv_smul (g : h.unitaryGroup) {D : ℕ} {La : AddSubgroup W}
    (hLa : IsDIntegral h D La) : IsDIntegral h D (g⁻¹ • La) := by
  set γ : W ≃ₗ[E] W := ((g⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) with hγ
  have hinj : Function.Injective (DistribMulAction.toAddMonoidEnd (W ≃ₗ[E] W) W γ) :=
    fun x y hxy => γ.injective hxy
  have hrel : (g⁻¹ • La).relIndex (dualLattice h (g⁻¹ • La)) =
      La.relIndex (dualLattice h La) := by
    rw [dualLattice_inv_smul]
    change (γ • La).relIndex (γ • dualLattice h La) = _
    rw [AddSubgroup.pointwise_smul_def, AddSubgroup.pointwise_smul_def]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a x hx
    rw [mem_inv_smul_iff] at hx ⊢
    rw [unitary_smul_scalar_smul]
    exact hLa.isLattice.smul_mem a _ hx
  · have hfg := hLa.isLattice.fg
    change (γ • La).FG
    rw [AddSubgroup.pointwise_smul_def]
    rw [AddSubgroup.fg_iff_exists_fin_addMonoidHom] at hfg ⊢
    obtain ⟨k, f, hf⟩ := hfg
    exact ⟨k, γ.toLinearMap.toAddMonoidHom.comp f, by
      rw [AddMonoidHom.range_comp, hf]
      rfl⟩
  · have hset : ((g⁻¹ • La : AddSubgroup W) : Set W) =
        γ.toLinearMap '' (La : Set W) := by
      ext y
      constructor
      · intro hy
        exact ⟨g • y, mem_inv_smul_iff.1 hy, inv_smul_smul g y⟩
      · rintro ⟨x, hx, rfl⟩
        change g⁻¹ • x ∈ g⁻¹ • La
        rw [mem_inv_smul_iff, smul_inv_smul]
        exact hx
    rw [hset, Submodule.span_image, hLa.isLattice.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top]
    exact LinearEquiv.surjective _
  · intro x hx y hy
    rw [mem_inv_smul_iff] at hx hy
    rw [← sesq_unitary_smul g]
    exact hLa.integral _ hx _ hy
  · rw [hrel]
    exact hLa.index_ne_zero
  · rw [hrel]
    exact hLa.index_le

end Transport

theorem AdaptedReduction.proof (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : HyperbolicPairTransitive.Statement h) (h₂ : LineNormalForm.Statement h)
    (h₃ : ComplementLattice.Statement h) : AdaptedReduction.Statement h := by
  intro v₀ w₀ hp h' hh' D
  obtain ⟨KK, hKK, n, hn, H⟩ := h₂ D
  obtain ⟨D', hD'⟩ := h₃ v₀ w₀ hp h' hh' D n hn
  refine ⟨KK, hKK, n, D', hn, fun La l hLa hl => ?_⟩
  obtain ⟨v, w, hvl, hvw, hK, hdec⟩ := H La l hLa hl
  obtain ⟨g, hgv, hgw⟩ := h₁ v₀ w₀ v w hp hvw
  have hI : lineCoeffs (E := E) (g⁻¹ • La) v₀ = lineCoeffs (E := E) La v := by
    rw [lineCoeffs_inv_smul, hgv]
  have hJ : lineCoeffs (E := E) (g⁻¹ • La) w₀ = lineCoeffs (E := E) La w := by
    rw [lineCoeffs_inv_smul, hgw]
  have hwv : h.toSesq w v = 1 := by
    rw [← h.isSymm.eq v w, hvw.2.2, map_one]
  have hsplit : ∀ x ∈ g⁻¹ • La, ∃ a ∈ lineCoeffs (E := E) (g⁻¹ • La) v₀,
      ∃ b ∈ lineCoeffs (E := E) (g⁻¹ • La) w₀,
        n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀ := by
    intro x hx
    rw [mem_inv_smul_iff] at hx
    obtain ⟨ha, hb⟩ := hdec _ hx
    refine ⟨(n : E) * h.toSesq w (g • x), by rw [hI]; exact ha,
      (n : E) * h.toSesq v (g • x), by rw [hJ]; exact hb, ?_⟩
    rw [mem_hypComplement, ← sesq_unitary_smul g v₀, ← sesq_unitary_smul g w₀, hgv, hgw,
      ← Nat.cast_smul_eq_nsmul E, smul_sub, smul_sub, unitary_smul_scalar_smul, unitary_smul_scalar_smul,
      unitary_smul_scalar_smul, hgv, hgw]
    simp only [map_sub, map_smul, smul_eq_mul, hvw.1, hvw.2.1, hvw.2.2, hwv]
    constructor <;> ring
  refine ⟨g, g⁻¹ • La, smul_inv_smul g La, hgv ▸ hvl, ?_, hsplit,
    hD' _ (isDIntegral_inv_smul g hLa) hsplit⟩
  rw [hI, hJ]
  exact hK

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchUnimodular
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic GroundTheory.Heights₂.Theta Module Matrix MeasureTheory
open scoped NNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ArchUnimodular

abbrev sigP (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) : ℕ :=
  posEigenCount (GramAtData.proof h v w).1

abbrev sigQ (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) : ℕ :=
  negEigenCount (GramAtData.proof h v w).1

def placeEquiv (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) :
    unitaryGroupMatrix (starRingEnd ℂ) (gramAt h v w) ≃ₜ*
      indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
  unitaryHermitianEquiv (hH := (GramAtData.proof h v w).1) (GramAtData.proof h v w).2

def fromPi (h : HermitianForm F E W) (v : Basis ι E W) :
    (∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w)) →*
      archUnitary h v where
  toFun f := ⟨fun w => ((placeEquiv h v w).symm (f w) : GL ι ℂ),
    (Subgroup.mem_pi _).2 fun w _ => ((placeEquiv h v w).symm (f w)).2⟩
  map_one' := by
    apply Subtype.ext
    funext w
    simp
  map_mul' f g := by
    apply Subtype.ext
    funext w
    simp

theorem continuous_fromPi (h : HermitianForm F E W) (v : Basis ι E W) :
    Continuous (fromPi h v) :=
  Continuous.subtype_mk (continuous_pi fun w => continuous_subtype_val.comp
    ((placeEquiv h v w).symm.continuous.comp (continuous_apply w))) _

theorem mulEquivHaarChar_conjCME_eq_one_of_reflect {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {t j : G} (hjj : j * j = 1) (hjt : j * t * j = t⁻¹) : mulEquivHaarChar (conjCME t) = 1 := by
  have hJ : mulEquivHaarChar (conjCME j) * mulEquivHaarChar (conjCME j) = 1 := by
    rw [← mulEquivHaarChar_conjCME_mul, hjj, conjCME_one, mulEquivHaarChar_refl]
  have h1 : mulEquivHaarChar (conjCME t⁻¹) = mulEquivHaarChar (conjCME t) := by
    rw [← hjt, mulEquivHaarChar_conjCME_mul, mulEquivHaarChar_conjCME_mul]
    calc mulEquivHaarChar (conjCME j) * mulEquivHaarChar (conjCME t) *
          mulEquivHaarChar (conjCME j)
        = mulEquivHaarChar (conjCME t) *
            (mulEquivHaarChar (conjCME j) * mulEquivHaarChar (conjCME j)) := by ring
      _ = mulEquivHaarChar (conjCME t) := by rw [hJ, mul_one]
  have h2 := mulEquivHaarChar_conjCME_inv t
  rw [h1] at h2
  have h3 : ((mulEquivHaarChar (conjCME t) : ℝ≥0) : ℝ) * (mulEquivHaarChar (conjCME t) : ℝ) = 1 := by
    exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (mulEquivHaarChar (conjCME t) : ℝ) := NNReal.coe_nonneg _
  have h5 : ((mulEquivHaarChar (conjCME t) : ℝ≥0) : ℝ) = 1 := by nlinarith
  exact_mod_cast h5

theorem mulEquivHaarChar_conjCME_archUnitary (h : HermitianForm F E W) (v : Basis ι E W)
    (g : archUnitary h v) : mulEquivHaarChar (conjCME g) = 1 := by
  let f : ∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
    fun w => placeEquiv h v w ⟨g.1 w, (Subgroup.mem_pi _).1 g.2 w trivial⟩
  have hg : fromPi h v f = g := by
    apply Subtype.ext
    funext w
    simp [fromPi, f]
  let ks := fun w => cartanHomeomorph.symm (f w)
  let k : ∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
    fun w => ((ks w).1 : indefiniteUnitaryGroup _ _)
  let s : ∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
    fun w => upqOfMatrix (ks w).2.1 (ks w).2.2.2
  let Jm : ∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
    fun w => indefJElem _ _
  have hfks : f = k * s := funext fun w => (cartanHomeomorph.apply_symm_apply (f w)).symm
  have eJ : Jm * Jm = 1 := funext fun w => indefJElem_mul_self
  have eS : Jm * s * Jm = s⁻¹ := funext fun w => indefJElem_mul_mul_indefJElem (ks w).2
  let K : Subgroup (archUnitary h v) :=
    (Subgroup.pi Set.univ fun w : InfinitePlace E =>
      maxCompact (indefiniteUnitaryGroup (sigP h v w) (sigQ h v w))).map (fromPi h v)
  have hK : IsCompact (K : Set (archUnitary h v)) := by
    rw [Subgroup.coe_map, Subgroup.coe_pi]
    exact (isCompact_univ_pi fun w => isCompact_maxCompact_indefiniteUnitary).image
      (continuous_fromPi h v)
  have hk : fromPi h v k ∈ K :=
    Subgroup.mem_map_of_mem _ ((Subgroup.mem_pi _).2 fun w _ => (ks w).1.2)
  have hjj : fromPi h v Jm * fromPi h v Jm = 1 := by rw [← map_mul, eJ, map_one]
  have hjt : fromPi h v Jm * fromPi h v s * fromPi h v Jm = (fromPi h v s)⁻¹ := by
    rw [← map_mul, ← map_mul, eS, map_inv]
  rw [← hg, hfks, map_mul, mulEquivHaarChar_conjCME_mul, mulEquivHaarChar_conjCME_eq_one hK hk,
    one_mul]
  exact mulEquivHaarChar_conjCME_eq_one_of_reflect hjj hjt

end ArchUnimodular

theorem ArchUnimodular.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchUnimodular.Statement h v := by
  intro μ _
  refine ⟨fun g => ?_⟩
  have hc : μ.map (conjCME g⁻¹) = μ := by
    have e := mulEquivHaarChar_smul_map μ (conjCME g⁻¹)
    rwa [ArchUnimodular.mulEquivHaarChar_conjCME_archUnitary, one_smul] at e
  have hfun : (fun x => x * g) = (fun x => g * x) ∘ (conjCME g⁻¹) := by
    funext x
    change x * g = g * (g⁻¹ * x * (g⁻¹)⁻¹)
    simp [mul_assoc]
  have hm : Measurable (conjCME g⁻¹) := (map_continuous (conjCME g⁻¹)).measurable
  rw [hfun, ← Measure.map_map (measurable_const_mul g) hm, hc, map_mul_left_eq_self]

section Example

open GaussianPlane

end Example

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open GroundTheory.Automorphic

noncomputable section

namespace ComplementExtension

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable {h : HermitianForm F E W} {v w : W}

theorem toSesq_v_v (hp : IsHyperbolicPair h v w) : h.toSesq v v = 0 := hp.1

theorem toSesq_w_w (hp : IsHyperbolicPair h v w) : h.toSesq w w = 0 := hp.2.1

theorem toSesq_v_w (hp : IsHyperbolicPair h v w) : h.toSesq v w = 1 := hp.2.2

theorem toSesq_w_v (hp : IsHyperbolicPair h v w) : h.toSesq w v = 1 := by
  rw [← h.isSymm.eq v w, hp.2.2, map_one]

theorem toSesq_swap_eq_zero {u z : W} (hz : h.toSesq u z = 0) : h.toSesq z u = 0 := by
  rw [← h.isSymm.eq u z, hz, map_zero]

def proj (hp : IsHyperbolicPair h v w) : W →ₗ[E] hypComplement h v w :=
  LinearMap.codRestrict _
    (LinearMap.id - (h.toSesq w).smulRight v - (h.toSesq v).smulRight w)
    (fun x => by
      rw [mem_hypComplement]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul,
        smul_eq_mul, toSesq_v_v hp, toSesq_w_w hp, toSesq_v_w hp, toSesq_w_v hp]
      constructor <;> ring)

theorem proj_apply (hp : IsHyperbolicPair h v w) (x : W) :
    (proj hp x : W) = x - h.toSesq w x • v - h.toSesq v x • w := rfl

theorem split (hp : IsHyperbolicPair h v w) (x : W) :
    h.toSesq w x • v + (proj hp x : W) + h.toSesq v x • w = x := by
  rw [proj_apply]; abel

theorem toSesq_split (hp : IsHyperbolicPair h v w) (a b a' b' : E) (z z' : hypComplement h v w) :
    h.toSesq (a • v + (z : W) + b • w) (a' • v + (z' : W) + b' • w) =
      conjHom F E a * b' + conjHom F E b * a' + h.toSesq z z' := by
  obtain ⟨hvz, hwz⟩ := mem_hypComplement.1 z.2
  obtain ⟨hvz', hwz'⟩ := mem_hypComplement.1 z'.2
  have hzv := toSesq_swap_eq_zero hvz
  have hzw := toSesq_swap_eq_zero hwz
  simp only [map_add (f := _), LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, toSesq_v_v hp, toSesq_w_w hp, toSesq_v_w hp, toSesq_w_v hp, hvz', hwz', hzv, hzw]
  ring

def extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) : W →ₗ[E] W :=
  (h.toSesq w).smulRight v + (hypComplement h v w).subtype ∘ₗ m ∘ₗ proj hp +
    (h.toSesq v).smulRight w

theorem extMap_apply (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    extMap hp m x = h.toSesq w x • v + (m (proj hp x) : W) + h.toSesq v x • w := rfl

theorem toSesq_w_extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    h.toSesq w (extMap hp m x) = h.toSesq w x := by
  have := (mem_hypComplement.1 (m (proj hp x)).2).2
  simp only [extMap_apply, map_add (f := _), map_smul, smul_eq_mul, toSesq_w_w hp, toSesq_w_v hp, this]
  ring

theorem toSesq_v_extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    h.toSesq v (extMap hp m x) = h.toSesq v x := by
  have := (mem_hypComplement.1 (m (proj hp x)).2).1
  simp only [extMap_apply, map_add (f := _), map_smul, smul_eq_mul, toSesq_v_v hp, toSesq_v_w hp, this]
  ring

theorem proj_extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    proj hp (extMap hp m x) = m (proj hp x) := by
  apply Subtype.ext
  rw [proj_apply, toSesq_w_extMap, toSesq_v_extMap, extMap_apply]
  abel

theorem extMap_comp (hp : IsHyperbolicPair h v w)
    (m m' : hypComplement h v w →ₗ[E] hypComplement h v w) :
    extMap hp m ∘ₗ extMap hp m' = extMap hp (m ∘ₗ m') := by
  ext x
  rw [LinearMap.comp_apply, extMap_apply hp m, toSesq_w_extMap, toSesq_v_extMap, proj_extMap,
    extMap_apply]
  rfl

theorem extMap_id (hp : IsHyperbolicPair h v w) : extMap hp LinearMap.id = LinearMap.id := by
  ext x
  rw [extMap_apply, LinearMap.id_apply, LinearMap.id_apply]
  exact split hp x

theorem proj_of_mem (hp : IsHyperbolicPair h v w) (x : hypComplement h v w) :
    proj hp (x : W) = x := by
  obtain ⟨hvx, hwx⟩ := mem_hypComplement.1 x.2
  apply Subtype.ext
  rw [proj_apply, hvx, hwx]
  simp

theorem proj_v (hp : IsHyperbolicPair h v w) : proj hp v = 0 := by
  apply Subtype.ext
  rw [proj_apply, toSesq_w_v hp, hp.1]
  simp

theorem proj_w (hp : IsHyperbolicPair h v w) : proj hp w = 0 := by
  apply Subtype.ext
  rw [proj_apply, hp.2.1, hp.2.2]
  simp

theorem proof (h : HermitianForm F E W) : ComplementExtension.Statement h := by
  intro v w hp h' hh' m
  let M : hypComplement h v w ≃ₗ[E] hypComplement h v w := m
  let e : W ≃ₗ[E] W := LinearEquiv.ofLinearMap (extMap hp M.toLinearMap)
    (extMap hp M.symm.toLinearMap)
    (by rw [extMap_comp, LinearEquiv.comp_symm, extMap_id])
    (by rw [extMap_comp, LinearEquiv.symm_comp, extMap_id])
  have he : ∀ x, e x = extMap hp M.toLinearMap x := fun x => rfl
  have hM : ∀ a b, h.toSesq (M a : W) (M b : W) = h.toSesq (a : W) b := by
    intro a b
    rw [← hh', ← hh']
    exact m.2 a b
  have hmem : e ∈ h.unitaryGroup := by
    intro x y
    rw [he, he, extMap_apply, extMap_apply, toSesq_split hp]
    conv_rhs => rw [← split hp x, ← split hp y]
    rw [toSesq_split hp]
    simp only [LinearEquiv.coe_coe, hM]
  refine ⟨⟨e, hmem⟩, ?_, ?_, ?_⟩
  · change e v = v
    rw [he, extMap_apply, proj_v, map_zero, toSesq_w_v hp, hp.1]
    simp
  · change e w = w
    rw [he, extMap_apply, proj_w, map_zero, hp.2.1, hp.2.2]
    simp
  · intro x
    change e x = ((M x : hypComplement h v w) : W)
    obtain ⟨hvx, hwx⟩ := mem_hypComplement.1 x.2
    rw [he, extMap_apply, proj_of_mem, hvx, hwx]
    simp

end ComplementExtension

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StComplementArchCocompact
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def ComplementArchCocompact.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (La : AddSubgroup W) (x₀ w₀ : W) (m : ℕ),
    IsLattice (E := E) La → IsHyperbolicPair h x₀ w₀ → 0 < m →
    ∃ K : Set (InfinitePlace E → ι → ℂ), IsCompact K ∧ ∀ Y : InfinitePlace E → ι → ℂ,
      (∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0 ∧
        star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0) →
      ∃ y ∈ hypComplement h x₀ w₀, (∃ z ∈ La, y = m • z) ∧ Y - vecAt v y ∈ K

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StImaginaryLatticeCocompact
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable (F E : Type*) [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

def ImaginaryLatticeCocompact.Statement : Prop :=
  ∀ m : ℕ, 0 < m → ∃ R : ℝ, ∀ s : InfinitePlace E → ℝ, ∃ a : 𝓞 E,
    (m : E) * a + conj F E ((m : E) * a) = 0 ∧ ∀ w, |(w.embedding ((m : E) * a)).im - s w| ≤ R

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

