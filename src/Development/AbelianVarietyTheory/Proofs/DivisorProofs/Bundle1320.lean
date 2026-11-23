module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsRhoOfAtInf
section
open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

namespace GlobalTheory.ArchUniq

noncomputable def evIHom (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem evI_eq_evIHom {F : Type} [Field F] [NumberField F] (a : AF F) : evI F a = evIHom F a := rfl

theorem trace_evI_heis {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] {κ : Type} [Fintype κ]
    (x a b : κ → AF F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ b + ⅟(2 : AF F) * a ⬝ᵥ b)) =
      trP F κ (locV x) (locV b) + trP F κ (locV a) (locV b) / 2 := by
  have hdot : ∀ y : κ → AF F, evIHom F (y ⬝ᵥ b) = ∑ i, locV y i * locV b i := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul, locV, evI_eq_evIHom]
  have h2 : ∀ t : AF F, evIHom F (⅟(2 : AF F) * t) = (1 / 2 : ℝ) • evIHom F t := by
    intro t
    have h : (2 : ℝ) • evIHom F (⅟(2 : AF F) * t) = evIHom F t := by
      rw [two_smul, ← map_add (f := _), ← two_mul, ← mul_assoc, mul_invOf_self, one_mul]
    rw [← h, smul_smul]
    norm_num
  rw [evI_eq_evIHom, map_add (f := _), h2, hdot, hdot, map_add (f := _), map_smul, trP, trP, smul_eq_mul]
  ring

theorem acts_rho_of_at_inf : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {W' : Type} [AddCommGroup W'] [Module (AF F) W'] {Bf : W' → W' → AF F} {κ : Type} [Fintype κ]
      (dc : Darboux Bf κ) (w : W'), At (evI F) w → ∀ f f₁ : SInf F κ,
      ⇑f₁ = schrF (trP F κ) (locV (dc.e w).1, locV (dc.e w).2) ⇑f → Acts (evI F) (dc.rho ψ w) ⇑f ⇑f₁ := by
  intro F _ _ ψ hψ W' _ _ Bf κ _ dc w hw f f₁ hf r hr
  have hab : ∀ u : AF F, evI F u = 0 → u • dc.e w = 0 := fun u hu => by
    rw [← map_smul, hw u hu, map_zero]
  have ha : At (evI F) (dc.e w).1 := fun u hu => congrArg Prod.fst (hab u hu)
  have hb : At (evI F) (dc.e w).2 := fun u hu => congrArg Prod.snd (hab u hu)
  funext x
  have ht : At (evI F) (x ⬝ᵥ (dc.e w).2 + ⅟(2 : AF F) * (dc.e w).1 ⬝ᵥ (dc.e w).2) := fun u hu => by
    have h : ∀ y : κ → AF F, u * (y ⬝ᵥ (dc.e w).2) = 0 := fun y => by
      rw [← smul_eq_mul, ← dotProduct_smul, hb u hu, dotProduct_zero]
    rw [smul_eq_mul, mul_add, h, mul_left_comm, h, mul_zero, add_zero]
  have hloc : (fun i => evI F ((x + (dc.e w).1) i)) = locV x + locV (dc.e w).1 := by
    funext i
    simp only [Pi.add_apply, locV, evI_eq_evIHom, map_add (f := _)]
  simp only [Darboux.rho, schr, tens]
  rw [hψ.2.2 _ ht, trace_evI_heis, hr.1 x _ ha, hf, hloc, schrF]
  exact (mul_assoc _ _ _).symm

end GlobalTheory.ArchUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal Classical

namespace GlobalTheory.WeilL2Words

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def arch1 (z : mixedEmbedding.mixedSpace F) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z, 0)

def IsStdInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop :=
  ∃ ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ, (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) ∧
    ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)

def arch (x : κ → mixedEmbedding.mixedSpace F) : κ → AdeleRing (𝓞 F) F := fun i => arch1 F (x i)

def archPair (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) :=
  (arch F h.1, arch F h.2)

def archPart (a : κ → AdeleRing (𝓞 F) F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1

def l2A (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : ℝ≥0∞ :=
  @lintegral _ (borel _) μ fun y => ∫⁻ x, ‖Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2

variable [Invertible (2 : AdeleRing (𝓞 F) F)]

def dS (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : (κ → AdeleRing (𝓞 F) F) → ℂ :=
  fun a => deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) Φ a) 0

def word (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : (κ → AdeleRing (𝓞 F) F) → ℂ :=
  hs.foldr (fun h g => dS F ψ h g) Φ

theorem word_cons (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (h) (hs) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    word F ψ (h :: hs) Φ = dS F ψ h (word F ψ hs Φ) := rfl

end GlobalTheory.WeilL2Words

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactFundamentalSet
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
namespace GlobalTheory.AdeleCocompactExt

theorem exists_compact_adeleE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ K : Set (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), IsCompact K ∧ ∀ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ e : E, a - inclR (F := F) (AF F) e ∈ K := by
  intro F E _ _ _ _ _
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K₀, hK₀, hK⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  haveI : IsModuleTopology (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := ⟨rfl⟩
  haveI : IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := IsModuleTopology.isTopologicalRing (AF F) _
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hφ : Continuous B.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap
  refine ⟨B.equivFun.symm '' Set.pi Set.univ (fun _ => K₀),
    (isCompact_univ_pi fun _ => hK₀).image hφ, ?_⟩
  intro a
  choose x hx using fun k => hK (B.equivFun a k)
  refine ⟨∑ k, x k • b k, fun k => B.equivFun a k - algebraMap F (AF F) (x k), fun k _ => hx k, ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  funext k
  have h1 : B.equivFun (inclR (F := F) (AF F) (∑ k, x k • b k)) k = algebraMap F (AF F) (x k) := by
    rw [Module.Basis.equivFun_apply]
    show (B.repr ((1 : AF F) ⊗ₜ[F] (∑ k, x k • b k))) k = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp [b, Module.Basis.repr_sum_self]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Finsupp.single_apply, hj]) (by simp)]
    simp
  simp only [map_sub, Pi.sub_apply, h1]

end GlobalTheory.AdeleCocompactExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesRationalMatricesOntoRational
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps : ∀ (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N), (∀ x : Matrix (Fin m) (Fin n) D.host.E, ∃ y z : Fin N → D.host.F, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) → ∀ y z : Fin N → D.host.F, ∃ x : Matrix (Fin m) (Fin n) D.host.E, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := by
  intro D m n N e hrat y z
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  let I : Matrix (Fin m) (Fin n) D.host.E →ₗ[D.host.F] Matrix (Fin m) (Fin n) (AE D) :=
    (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toLinearMap.mapMatrix
  have hI : ∀ x, I x = incM D.host.F x := fun x => rfl
  let L : Matrix (Fin m) (Fin n) D.host.E →ₗ[D.host.F] VA D.host.F N := (e.toLinearMap.restrictScalars D.host.F).comp I
  have hL : ∀ x, L x = e (incM D.host.F x) := fun x => rfl
  let r : (Fin N → D.host.F) →ₗ[D.host.F] (Fin N → AF D.host.F) :=
    LinearMap.pi fun i => (Algebra.linearMap D.host.F (AF D.host.F)).comp (LinearMap.proj i)
  let R : ((Fin N → D.host.F) × (Fin N → D.host.F)) →ₗ[D.host.F] VA D.host.F N := LinearMap.prodMap r r
  have hR : ∀ y z, R (y, z) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun _ _ => rfl
  have hAinj : Function.Injective (algebraMap D.host.F (AF D.host.F)) := AdeleRing.algebraMap_injective _ _
  have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
  have hRinj : Function.Injective R := fun a b h => Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
  have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
    Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
  have hLinj : Function.Injective L := e.injective.comp hIinj
  have hle : LinearMap.range L ≤ LinearMap.range R := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y', z', h⟩ := hrat x
    exact ⟨(y', z'), by rw [hR, hL, h]⟩
  have hdim : Fintype.card (Fin m) * Fintype.card (Fin n) * Module.finrank D.host.F D.host.E = N + N := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at h1
    exact h1
  have hfin : Module.finrank D.host.F (LinearMap.range L) = Module.finrank D.host.F (LinearMap.range R) := by
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
      Module.finrank_prod, Module.finrank_fin_fun, hdim]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
  exact ⟨x, by rw [← hL, hx, hR]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousKeepParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicCoord

section Ad

variable (F : Type) [Field F] [NumberField F]

theorem fstA_pairA (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

variable {F} in
theorem af_ext {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext (α := Ainf F) (β := Af F) h1 h2

theorem pairA_mul_eq_zero_iff_snd (a : AF F) : pairA F 0 1 * a = 0 ↔ sndA F a = 0 := by
  constructor
  · intro h
    have := congrArg (sndA F) h
    rwa [map_mul, map_zero, sndA_pairA, one_mul] at this
  · intro h
    refine af_ext ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA, zero_mul]
    · rw [map_mul, map_zero, sndA_pairA, h, mul_zero]

theorem pairA_mul_eq_zero_iff_fst (a : AF F) : pairA F 1 0 * a = 0 ↔ fstA F a = 0 := by
  constructor
  · intro h
    have := congrArg (fstA F) h
    rwa [map_mul, map_zero, fstA_pairA, one_mul] at this
  · intro h
    refine af_ext ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA, h, mul_zero]
    · rw [map_mul, map_zero, sndA_pairA, zero_mul]

def incF : Af F →ₗ[F] AF F where
  toFun y := pairA F 0 y
  map_add' y y' := af_ext (by rw [map_add (f := _), fstA_pairA, fstA_pairA, fstA_pairA, add_zero])
    (by rw [map_add (f := _), sndA_pairA, sndA_pairA, sndA_pairA])
  map_smul' c y := af_ext (by rw [map_smul, fstA_pairA, fstA_pairA, RingHom.id_apply, smul_zero])
    (by rw [map_smul, sndA_pairA, sndA_pairA, RingHom.id_apply])

def incI : Ainf F →ₗ[F] AF F where
  toFun y := pairA F y 0
  map_add' y y' := af_ext (by rw [map_add (f := _), fstA_pairA, fstA_pairA, fstA_pairA])
    (by rw [map_add (f := _), sndA_pairA, sndA_pairA, sndA_pairA, add_zero])
  map_smul' c y := af_ext (by rw [map_smul, fstA_pairA, fstA_pairA, RingHom.id_apply])
    (by rw [map_smul, sndA_pairA, sndA_pairA, RingHom.id_apply, smul_zero])

theorem incF_sndA (a : AF F) : incF F (sndA F a) = pairA F 0 1 * a :=
  af_ext (by rw [map_mul, fstA_pairA, zero_mul]; rfl) (by rw [map_mul, sndA_pairA, one_mul]; rfl)

theorem incI_fstA (a : AF F) : incI F (fstA F a) = pairA F 1 0 * a :=
  af_ext (by rw [map_mul, fstA_pairA, one_mul]; rfl) (by rw [map_mul, sndA_pairA, zero_mul]; rfl)

end Ad

variable (D : D7)

def secF : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (incF D.host.F) LinearMap.id

def secI : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (incI D.host.F) LinearMap.id

theorem secF_finPart (z : AE D) : secF D (finPart D z) = pairA D.host.F 0 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(finPart D).map_zero, (secF D).map_zero, smul_zero]
  | tmul a b =>
    have h1 : finPart D (a ⊗ₜ b) = sndA D.host.F a ⊗ₜ b := rfl
    rw [h1, secF, TensorProduct.map_tmul, LinearMap.id_apply, incF_sndA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add (finPart D), map_add (secF D), hx, hy, smul_add]

theorem secI_infPart (z : AE D) : secI D (infPart D z) = pairA D.host.F 1 0 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(infPart D).map_zero, (secI D).map_zero, smul_zero]
  | tmul a b =>
    have h1 : infPart D (a ⊗ₜ b) = fstA D.host.F a ⊗ₜ b := rfl
    rw [h1, secI, TensorProduct.map_tmul, LinearMap.id_apply, incI_fstA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add (infPart D), map_add (secI D), hx, hy, smul_add]

theorem finPart_smul (z : AE D) : finPart D (pairA D.host.F 0 1 • z) = finPart D z := by
  rw [Algebra.smul_def, (finPart D).map_mul]
  have : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show sndA D.host.F (algebraMap (AF D.host.F) (AF D.host.F) (pairA D.host.F 0 1)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, sndA_pairA]
    rfl
  rw [this, one_mul]

theorem infPart_smul (z : AE D) : infPart D (pairA D.host.F 1 0 • z) = infPart D z := by
  rw [Algebra.smul_def, (infPart D).map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show fstA D.host.F (algebraMap (AF D.host.F) (AF D.host.F) (pairA D.host.F 1 0)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, fstA_pairA]
    rfl
  rw [this, one_mul]

theorem finPart_eq_zero_iff (z : AE D) : finPart D z = 0 ↔ pairA D.host.F 0 1 • z = 0 := by
  constructor
  · intro h; rw [← secF_finPart, h, (secF D).map_zero]
  · intro h; rw [← finPart_smul, h, (finPart D).map_zero]

theorem infPart_eq_zero_iff (z : AE D) : infPart D z = 0 ↔ pairA D.host.F 1 0 • z = 0 := by
  constructor
  · intro h; rw [← secI_infPart, h, (secI D).map_zero]
  · intro h; rw [← infPart_smul, h, (infPart D).map_zero]

theorem smul_vec_fin {N : ℕ} (u : Fin N → AF D.host.F) : pairA D.host.F 0 1 • u = 0 ↔ GlobalTheory.SWQ.fin u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_snd D.host.F (u l)

theorem smul_vec_inf {N : ℕ} (u : Fin N → AF D.host.F) : pairA D.host.F 1 0 • u = 0 ↔ GlobalTheory.SWQ.inf u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_fst D.host.F (u l)

theorem smul_pair_eq_zero {N : ℕ} (c : AF D.host.F) (w : VA D.host.F N) : c • w = 0 ↔ c • w.1 = 0 ∧ c • w.2 = 0 :=
  Prod.ext_iff

theorem coord (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N) :
    Continuous e ∧ Continuous e.symm ∧
      (∀ x, x.map (finPart D) = 0 ↔ GlobalTheory.SWQ.fin (e x).1 = 0 ∧ GlobalTheory.SWQ.fin (e x).2 = 0) ∧
      (∀ x, x.map (infPart D) = 0 ↔ GlobalTheory.SWQ.inf (e x).1 = 0 ∧ GlobalTheory.SWQ.inf (e x).2 = 0) := by
  haveI h0 : IsModuleTopology (AF D.host.F) (AE D) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI h1 : IsModuleTopology (AF D.host.F) (Fin n → AE D) := IsModuleTopology.instPi
  haveI h2 : IsModuleTopology (AF D.host.F) (Matrix (Fin m) (Fin n) (AE D)) := IsModuleTopology.instPi
  refine ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap,
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, fun x => ?_, fun x => ?_⟩
  · have key : x.map (finPart D) = 0 ↔ pairA D.host.F 0 1 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => finPart_eq_zero_iff D (x i j)
    rw [key, ← smul_vec_fin, ← smul_vec_fin, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]
  · have key : x.map (infPart D) = 0 ↔ pairA D.host.F 1 0 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => infPart_eq_zero_iff D (x i j)
    rw [key, ← smul_vec_inf, ← smul_vec_inf, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]

end GlobalTheory.AdelicCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section
open scoped Classical

namespace GlobalTheory.ConjSch

def conjSchwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := starRingEnd ℂ (f x)
  smooth' := Complex.conjCLE.contDiff.comp f.smooth'
  decay' k n := by
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => starRingEnd ℂ (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := by
      funext y; simp
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem conjSchwartz_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjSchwartz f x = starRingEnd ℂ (f x) := rfl

theorem conj_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => starRingEnd ℂ (Φ x)) ∈ schA F κ := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, g, hg, rfl⟩ := hΨ
    apply Submodule.subset_span
    refine ⟨conjSchwartz f, fun y => starRingEnd ℂ (g y), ⟨hg.1.comp _, hg.2.comp_left (map_zero _)⟩, ?_⟩
    funext x
    simp [pureA, conjSchwartz_apply, map_mul]
  | zero =>
    convert (schA F κ).zero_mem using 1
    funext x; simp
  | add Ψ₁ Ψ₂ _ _ h₁ h₂ =>
    have := (schA F κ).add_mem h₁ h₂
    convert this using 1
    funext x; simp
  | smul c Ψ _ h =>
    have := (schA F κ).smul_mem (starRingEnd ℂ c) h
    convert this using 1
    funext x; simp

end GlobalTheory.ConjSch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartSmooth
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.ChartSmooth

theorem isStandardSmooth_C (k : Type) [CommRing k] (D : ℕ) :
    (algebraMap k (MvPolynomial (Fin D) k)).IsStandardSmoothOfRelativeDimension D := by
  let P₀ : Algebra.Presentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := Algebra.Generators.mvPolynomial k (Fin D)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).2
    (P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension]))

theorem isStandardSmooth_algX {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {D : ℕ}
    {U : X.Opens} (x : Fin D → Γ(X, U)) (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    (algX p U).IsStandardSmoothOfRelativeDimension D := by
  have hC : (MvPolynomial.eval₂Hom (algX p U) x).comp (algebraMap k _) = algX p U :=
    RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ a
  have h := (RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.1 hx).comp
    (isStandardSmooth_C k D)
  rwa [hC, zero_add] at h

theorem smooth_of_etale {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {D : ℕ}
    {U : X.Opens} (hU : IsAffineOpen U) (x : Fin D → Γ(X, U))
    (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    SmoothOfRelativeDimension D (U.ι ≫ p) := by
  have hA : IsAffine U.toScheme := hU
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv (isStandardSmooth_algX p x hx)
  have h₂ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    U.topIso.symm.commRingCatIsoToRingEquiv h₁
  refine (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension D)).2
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_)
  have e : (U.ι ≫ p).appTop = (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (by simp) ≫ U.topIso.inv := by
    rw [Iso.hom_inv_id_assoc]
    simp only [Scheme.Hom.appTop, Scheme.Hom.appLE, Scheme.Hom.comp_app, Scheme.Opens.topIso_inv,
      Scheme.Opens.ι_app, Category.assoc]
    exact (congrArg (p.app ⊤ ≫ ·) (Eq.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))
      (X.presheaf.map_comp _ _))).trans (Category.assoc _ _ _).symm
  rw [e]
  exact h₂

end GlobalTheory.ChartSmooth
end

