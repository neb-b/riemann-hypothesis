module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0010
public import GroundTheory.AutomorphicForms.Bundle0011
public import GroundTheory.AutomorphicForms.HeckeAlgebra
public import GroundTheory.AutomorphicForms.Bundle0004
public import GroundTheory.AutomorphicForms.DixmierMalliavinHaar
public import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
public import GroundTheory.AutomorphicForms.Bundle0012
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import GroundTheory.AutomorphicForms.Iwasawa

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.CompactModCentre
section
noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace SchurOrthogonality

open MeasureTheory Topology Set Function ComplexConjugate Module

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

theorem span_orbit_eq_top [π.IsIrreducible] {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (range fun g => π g v) = ⊤ := by
  set S := Submodule.span ℂ (range fun g => π g v)
  have hS : ∀ g, ∀ ⦃x⦄, x ∈ S → π g x ∈ S := by
    intro g x hx
    have : S ≤ S.comap (π g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp [Module.End.mul_apply]⟩)
    exact this hx
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨S, hS⟩ : Subrepresentation π) with h | h
  · exfalso
    apply hv
    have : v ∈ (⟨S, hS⟩ : Subrepresentation π).toSubmodule := Submodule.subset_span ⟨1, by simp⟩
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · exact congrArg Subrepresentation.toSubmodule h

variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {Z : Subgroup G} [Z.Normal]

variable [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)] {ν : Measure (G ⧸ Z)}

section Characters

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Characters

section Orthogonality

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
  {Z : Subgroup G} [Z.Normal] [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)]
  {ν : Measure (G ⧸ Z)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant] [CompactSpace (G ⧸ Z)]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}


end Orthogonality

end SchurOrthogonality

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.DixmierMalliavinHaarDensity
section
namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open MeasureTheory Metric Set Filter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
  [μ.IsHaarMeasure]

theorem exists_smooth_density_prodExp {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ ε > 0, ∀ K : (Fin d → ℝ) → ℂ, ContDiff ℝ ∞ K → tsupport K ⊆ closedBall 0 ε →
      ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧
        HasCompactSupport κ ∧
        ∀ φ : G → ℂ, Continuous φ → ∫ y, κ y * φ y ∂μ = ∫ t, K t * φ (h.prodExp (⇑b) t) := by
  obtain ⟨r, ρ, c, W, hr, hρ, hρpos, hW, hPW, hcP, hc, hint⟩ := h.exists_haar_density_prodExp μ b
  set P := h.prodExp (⇑b) with hPdef
  have hPc : Continuous P := h.continuous_prodExp _
  refine ⟨r / 2, by positivity, fun K hK hKs => ?_⟩
  have hεr : closedBall (0 : Fin d → ℝ) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (by linarith)
  set C := P '' closedBall (0 : Fin d → ℝ) (r / 2) with hCdef
  have hCc : IsCompact C := (isCompact_closedBall _ _).image hPc
  let κ : G → ℂ := W.indicator fun y => K (c y) * (((ρ (c y))⁻¹ : ℝ) : ℂ)
  have hκC : ∀ y, y ∉ C → κ y = 0 := by
    intro y hy
    by_cases hyW : y ∈ W
    · have hz : c y ∉ closedBall (0 : Fin d → ℝ) (r / 2) := fun hz => hy ⟨c y, hz, hcP y hyW⟩
      have : K (c y) = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hKs h')
      simp [κ, indicator_of_mem hyW, this]
    · simp [κ, indicator_of_notMem hyW]
  have hκsupp : tsupport κ ⊆ C :=
    closure_minimal (fun y hy => by_contra fun h' => hy (hκC y h')) hCc.isClosed
  have hκW : ∀ z ∈ ball (0 : Fin d → ℝ) r, κ (P z) * (ρ z : ℂ) = K z := by
    intro z hz
    obtain ⟨hzW, hcz⟩ := hPW z hz
    have hρz : (ρ z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hρpos z hz).ne'
    simp only [κ, indicator_of_mem hzW, hcz, Complex.ofReal_inv]
    field_simp
  have hsmooth : (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) := by
    intro g
    rw [h.contMDiffAt_iff_expG]
    have hcont : Continuous (fun Y : 𝔤 => g * h.expG Y) :=
      continuous_const.mul h.continuous_expG
    have hg0 : g * h.expG 0 = g := by rw [h.expG_zero, mul_one]
    by_cases hg : g ∈ C
    · obtain ⟨z₀, hz₀, rfl⟩ := hg
      have hz₀r : z₀ ∈ ball (0 : Fin d → ℝ) r := hεr hz₀
      obtain ⟨hgW, hcg⟩ := hPW z₀ hz₀r
      have hev : (fun Y : 𝔤 => κ (P z₀ * h.expG Y)) =ᶠ[𝓝 0]
          fun Y => K (c (P z₀ * h.expG Y)) * (((ρ (c (P z₀ * h.expG Y)))⁻¹ : ℝ) : ℂ) := by
        have : ∀ᶠ Y in 𝓝 (0 : 𝔤), P z₀ * h.expG Y ∈ W := by
          have := hcont.continuousAt (x := 0)
          rw [ContinuousAt, hg0] at this
          exact this (hW.mem_nhds hgW)
        filter_upwards [this] with Y hY
        simp [κ, indicator_of_mem hY]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have hc0 := hc (P z₀) hgW
      have hρ0 : ρ (c (P z₀ * h.expG 0)) ≠ 0 := by
        rw [hg0, hcg]; exact (hρpos z₀ hz₀r).ne'
      exact (hK.contDiffAt.comp _ hc0).mul
        ((Complex.ofRealCLM.contDiff.contDiffAt).comp _ ((hρ.contDiffAt.comp _ hc0).inv hρ0))
    · have hev : (fun Y : 𝔤 => κ (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => 0 := by
        have : ∀ᶠ Y in 𝓝 (0 : 𝔤), g * h.expG Y ∈ Cᶜ := by
          have := hcont.continuousAt (x := 0)
          rw [ContinuousAt, hg0] at this
          exact this (hCc.isClosed.isOpen_compl.mem_nhds hg)
        filter_upwards [this] with Y hY
        exact hκC _ hY
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hκc : Continuous κ := by
    let := h.chartedSpace
    exact hsmooth.continuous
  refine ⟨κ, hsmooth, HasCompactSupport.intro hCc hκC, fun φ hφ => ?_⟩
  have hψ₀s : tsupport (fun y => κ y * φ y) ⊆ P '' ball 0 r :=
    (tsupport_mul_subset_left).trans (hκsupp.trans (image_mono hεr))
  rw [hint (fun y => κ y * φ y) (hκc.mul hφ)
    ((HasCompactSupport.intro hCc hκC).mul_right) hψ₀s]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun t => K t * φ (P t))
    (s := ball (0 : Fin d → ℝ) r) fun z hz => by
      have : K z = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hεr (hKs h'))
      simp [this]]
  refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
  rw [mul_right_comm, hκW z hz]

end IsExpLieAlgebra

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.HermitianDisc
section
noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix GroundTheory.LocalField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']

namespace HermitianForm

variable [Algebra.IsSeparable F E]

def detUnit (h : HermitianForm F E V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι E V) : Fˣ := by
  have hdet : (gram h.toSesq b).det ∈ Set.range (algebraMap F E) := by
    apply conj_eq_self_iff.1
    rw [← conjHom_apply, RingHom.map_det, RingHom.mapMatrix_apply, ← det_transpose,
      isHermitianFor_gram h b]
  exact Units.mk0 hdet.choose (by
    intro h0
    have heq := hdet.choose_spec
    rw [h0, map_zero] at heq
    exact (isUnit_det_gram h b).ne_zero heq.symm)

end HermitianForm

def diagForm {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → Fˣ) :
    HermitianForm F E (ι → E) where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E)
    (fun x y => ∑ i, conj F E (x i) * algebraMap F E (a i) * y i)
    (fun x x' y => by simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, conjHom_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
  isSymm := ⟨fun x y => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.mk₂'ₛₗ_apply, conjHom_apply, map_sum, map_mul, conj_conj,
      conj_algebraMap]
    exact Finset.sum_congr rfl fun i _ => by ring⟩
  nonsingular := by
    have ha : ∀ i, algebraMap F E (a i) ≠ 0 := fun i => by simp
    have key : ∀ (x : ι → E) (j : ι),
        (∑ i, conj F E (x i) * algebraMap F E (a i) * (Pi.single j 1 : ι → E) i) =
          conj F E (x j) * algebraMap F E (a j) := by
      intro x j
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [Pi.single_apply, hij]
      · simp
    constructor
    · intro x y hxy
      funext j
      have h1 := LinearMap.congr_fun hxy (Pi.single j 1)
      simp only [LinearMap.mk₂'ₛₗ_apply, key] at h1
      have h2 := mul_right_cancel₀ (ha j) h1
      rw [← conj_conj (F := F) (x j), h2, conj_conj]
    · intro f
      refine ⟨fun j => conj F E (f (Pi.single j 1) * (algebraMap F E (a j))⁻¹),
        LinearMap.ext fun y => ?_⟩
      simp only [LinearMap.mk₂'ₛₗ_apply, conj_conj]
      conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ f y]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : (fun j => if i = j then (1 : E) else 0) = Pi.single i 1 := by
        funext j; simp [Pi.single_apply, eq_comm]
      rw [this, smul_eq_mul]
      field_simp [ha i]

end GroundTheory.Automorphic

end
end

-- bundled from GroundTheory.AutomorphicForms.InductionParabolicGroups
section
noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa

variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)

def blockDiagPart (A : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => if β i = β j then A i j else 0

variable {F n β}

theorem blockDiagPart_apply (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    blockDiagPart F n β A i j = if β i = β j then A i j else 0 := rfl

theorem blockDiagPart_one : blockDiagPart F n β 1 = 1 := by
  ext i j
  rw [blockDiagPart_apply]
  split_ifs with h
  · rfl
  · rw [one_apply_ne fun hij => h (by rw [hij])]

theorem blockDiagPart_mul {A B : Matrix (Fin n) (Fin n) F} (hA : A.BlockTriangular β)
    (hB : B.BlockTriangular β) :
    blockDiagPart F n β (A * B) = blockDiagPart F n β A * blockDiagPart F n β B := by
  ext i j
  simp only [blockDiagPart_apply, Matrix.mul_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : β i = β k
    · rw [if_pos hk, if_pos (hk.symm.trans h)]
    · rw [if_neg hk, zero_mul]
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [hB (h ▸ hlt : β j < β k), mul_zero]
      · rw [hA hlt, zero_mul]
  · refine (Finset.sum_eq_zero fun k _ => ?_).symm
    by_cases hk : β i = β k
    · rw [if_neg fun h' => h (hk.trans h'), mul_zero]
    · rw [if_neg hk, zero_mul]

theorem blockDiagPart_of_forall {A : Matrix (Fin n) (Fin n) F}
    (hA : ∀ i j, β i ≠ β j → A i j = 0) : blockDiagPart F n β A = A := by
  ext i j
  rw [blockDiagPart_apply]
  split_ifs with h
  · rfl
  · exact (hA i j h).symm

variable (F n β)

def levi : Subgroup (GL (Fin n) F) :=
  blockUpper F n β ⊓ blockUpper F n (OrderDual.toDual ∘ β)

variable {F n β}

theorem mem_levi {g : GL (Fin n) F} :
    g ∈ levi F n β ↔ ∀ i j, β i ≠ β j → g i j = 0 := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2 (show OrderDual.toDual (β j) < OrderDual.toDual (β i) from h)
    · exact h1 h
  · intro h
    exact ⟨fun i j hij => h i j hij.ne', fun i j hij => h i j
      (show β i < β j from hij).ne⟩

theorem levi_le_blockUpper : levi F n β ≤ blockUpper F n β := inf_le_left

theorem diagGL_mem_levi (d : Fin n → Fˣ) : diagGL F n d ∈ levi F n β := by
  rw [mem_levi]
  intro i j hij
  have : i ≠ j := fun h => hij (h ▸ rfl)
  simp [diagonal_apply_ne _ this]

def leviProjFun (p : blockUpper F n β) : GL (Fin n) F where
  val := blockDiagPart F n β (p : GL (Fin n) F)
  inv := blockDiagPart F n β ((p⁻¹ : blockUpper F n β) : GL (Fin n) F)
  val_inv := by
    rw [← blockDiagPart_mul p.2 (p⁻¹).2, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one, blockDiagPart_one]
  inv_val := by
    rw [← blockDiagPart_mul (p⁻¹).2 p.2, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, Units.val_one, blockDiagPart_one]

theorem leviProjFun_mem (p : blockUpper F n β) : leviProjFun p ∈ levi F n β := by
  rw [mem_levi]
  intro i j hij
  show blockDiagPart F n β _ i j = 0
  rw [blockDiagPart_apply, if_neg hij]

variable (F n β)

def leviProj : blockUpper F n β →* levi F n β where
  toFun p := ⟨leviProjFun p, leviProjFun_mem p⟩
  map_one' := Subtype.ext (Units.ext (by
    show blockDiagPart F n β ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
    rw [Units.val_one, blockDiagPart_one]))
  map_mul' p q := Subtype.ext (Units.ext (by
    show blockDiagPart F n β (((p * q : blockUpper F n β) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = blockDiagPart F n β (p : GL (Fin n) F) *
        blockDiagPart F n β (q : GL (Fin n) F)
    rw [Subgroup.coe_mul, Units.val_mul, blockDiagPart_mul p.2 q.2]))

variable {F n β}

theorem leviProj_apply (p : blockUpper F n β) (i j : Fin n) :
    ((leviProj F n β p : levi F n β) : GL (Fin n) F) i j =
      if β i = β j then (p : GL (Fin n) F) i j else 0 := rfl

theorem leviProj_of_mem_levi {m : GL (Fin n) F} (hm : m ∈ levi F n β) :
    leviProj F n β ⟨m, levi_le_blockUpper hm⟩ = ⟨m, hm⟩ :=
  Subtype.ext (Units.ext (blockDiagPart_of_forall (mem_levi.1 hm)))

def leviIncl : levi F n β →* blockUpper F n β :=
  Subgroup.inclusion levi_le_blockUpper

theorem leviProj_leviIncl (m : levi F n β) : leviProj F n β (leviIncl m) = m :=
  leviProj_of_mem_levi m.2

variable (F n β)

def unipotentRadical : Subgroup (GL (Fin n) F) :=
  (leviProj F n β).ker.map (blockUpper F n β).subtype

def oppositeUnipotentRadical : Subgroup (GL (Fin n) F) :=
  unipotentRadical F n (OrderDual.toDual ∘ β)

variable {F n β}

theorem mem_unipotentRadical {g : GL (Fin n) F} :
    g ∈ unipotentRadical F n β ↔ g ∈ blockUpper F n β ∧
      ∀ i j, β i = β j → g i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.2, fun i j hij => ?_⟩
    have h := congrArg (fun m : levi F n β => ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)
      ((leviProj F n β).mem_ker.1 hp)
    simp only [leviProj_apply, if_pos hij] at h
    simpa using h
  · rintro ⟨hP, h⟩
    refine ⟨⟨g, hP⟩, (leviProj F n β).mem_ker.2 (Subtype.ext (Units.ext ?_)), rfl⟩
    ext i j
    show (if β i = β j then g i j else 0) = ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j
    split_ifs with hij
    · rw [h i j hij, Units.val_one]
    · rw [Units.val_one, one_apply_ne fun e => hij (by rw [e])]

theorem mem_oppositeUnipotentRadical {g : GL (Fin n) F} :
    g ∈ oppositeUnipotentRadical F n β ↔ (∀ i j, β i < β j → g i j = 0) ∧
      ∀ i j, β i = β j → g i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  rw [oppositeUnipotentRadical, mem_unipotentRadical, mem_blockUpper]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 (show OrderDual.toDual (β j) < OrderDual.toDual (β i)
      from hij), fun i j hij => h2 i j (by simpa using hij)⟩,
    fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 i j hij, fun i j hij => h2 i j (by simpa using hij)⟩⟩

theorem unipotentRadical_le_blockUpper : unipotentRadical F n β ≤ blockUpper F n β :=
  fun _ hg => (mem_unipotentRadical.1 hg).1

theorem mem_unipotentRadical_iff_leviProj {p : blockUpper F n β} :
    (p : GL (Fin n) F) ∈ unipotentRadical F n β ↔ leviProj F n β p = 1 := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    rw [← (Subtype.ext hqp : q = p)]
    exact hq
  · intro h
    exact ⟨p, h, rfl⟩

theorem conj_mem_unipotentRadical {p u : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (hu : u ∈ unipotentRadical F n β) : p * u * p⁻¹ ∈ unipotentRadical F n β := by
  have huP := unipotentRadical_le_blockUpper hu
  have h := (mem_unipotentRadical_iff_leviProj (p := ⟨u, huP⟩)).1 hu
  have hm : p * u * p⁻¹ ∈ blockUpper F n β :=
    (blockUpper F n β).mul_mem ((blockUpper F n β).mul_mem hp huP) ((blockUpper F n β).inv_mem hp)
  refine (mem_unipotentRadical_iff_leviProj (p := ⟨_, hm⟩)).2 ?_
  have : (⟨p * u * p⁻¹, hm⟩ : blockUpper F n β) = ⟨p, hp⟩ * ⟨u, huP⟩ * (⟨p, hp⟩)⁻¹ := rfl
  rw [this, map_mul, map_mul, h, mul_one, map_inv, mul_inv_cancel]

theorem leviProj_inv_mul_mem (p : blockUpper F n β) :
    ((leviIncl (leviProj F n β p))⁻¹ * p : blockUpper F n β).1 ∈ unipotentRadical F n β := by
  rw [mem_unipotentRadical_iff_leviProj, map_mul, map_inv, leviProj_leviIncl, inv_mul_cancel]

variable (F n) in
theorem diagGL_conj_apply (d : Fin n → Fˣ) (g : GL (Fin n) F) (i j : Fin n) :
    (diagGL F n d * g * (diagGL F n d)⁻¹ : GL (Fin n) F) i j =
      (d i : F) * g i j * ((d j)⁻¹ : Fˣ) := by
  rw [← map_inv]
  show ((diagGL F n d : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) *
    (diagGL F n d⁻¹ : Matrix (Fin n) (Fin n) F)) i j = _
  rw [coe_diagGL, coe_diagGL, mul_diagonal, diagonal_mul]
  rfl

variable (F n) in
theorem diagGL_inv_conj_apply (d : Fin n → Fˣ) (g : GL (Fin n) F) (i j : Fin n) :
    ((diagGL F n d)⁻¹ * g * diagGL F n d : GL (Fin n) F) i j =
      (((d i)⁻¹ : Fˣ) : F) * g i j * (d j : F) := by
  rw [← map_inv]
  show ((diagGL F n d⁻¹ : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) *
    (diagGL F n d : Matrix (Fin n) (Fin n) F)) i j = _
  rw [coe_diagGL, coe_diagGL, mul_diagonal, diagonal_mul]
  rfl


variable (β) in
def blockRank (i : Fin n) : ℕ := (Finset.univ.filter fun j => β j < β i).card

theorem blockRank_lt {i j : Fin n} (h : β i < β j) : blockRank β i < blockRank β j := by
  refine Finset.card_lt_card ⟨fun k hk => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.trans h
  · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)
    simp at this

theorem blockRank_eq {i j : Fin n} (h : β i = β j) : blockRank β i = blockRank β j := by
  simp [blockRank, h]

end Parabolic

end GroundTheory.Automorphic
end
end

