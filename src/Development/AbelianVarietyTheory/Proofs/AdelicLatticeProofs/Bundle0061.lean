module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RationalHermitianRankOneLatticeSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVac.RatDual

open Formalism.L2.Pj

variable {D : D7}

theorem mem_mul_of_trace (D : D7) (z : D.host.E)
    (h : ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n) :
    z ∈ D.host.AA * D.host.AAbar := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hξ := cmHost_imaginaryGenerator_ne_zero hP D
  have hz : D.host.xi0 * z ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.mem_dual
      (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
    intro a ha
    rw [FractionalIdeal.mem_one_iff] at ha
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨n, hn⟩ := h c
    rw [Algebra.traceForm_apply, mul_assoc, mul_comm z]
    exact ⟨n, (eq_intCast (algebraMap ℤ ℚ) _).trans hn.symm⟩
  rw [← dual_eq hP D] at hz
  have h4 := FractionalIdeal.mul_mem_mul
    (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹) hz
  have e1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹ *
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar) =
      D.host.AA * D.host.AAbar := by
    rw [mul_assoc, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ,
      FractionalIdeal.spanSingleton_one, one_mul]
  rwa [e1, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul] at h4

theorem mem_AA_of_trace (D : D7) (z : D.host.E)
    (h : ∀ a ∈ D.host.AA, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (star a * z)) = n) :
    z ∈ D.host.AA := by
  have hAb : D.host.AAbar ≠ 0 := by
    intro h
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h, mul_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z *
      D.host.AAbar ≤ D.host.AA * D.host.AAbar := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro b hb
    refine mem_mul_of_trace D _ fun c => ?_
    have hcb : (c : D.host.E) * b ∈ D.host.AAbar :=
      Submodule.smul_mem (D.host.AAbar : Submodule (𝓞 D.host.E) D.host.E) c hb
    have := h _ (conj_mem_AA D hcb)
    have hs : star (D.host.conj ((c : D.host.E) * b)) = (c : D.host.E) * b :=
      (bridge_star_holds D.R D.host _).trans (conj_conj D _)
    rwa [hs, mul_assoc, mul_comm b] at this
  have hle2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z ≤ D.host.AA := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z
        = D.host.AAbar⁻¹ * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E))
            z * D.host.AAbar) := by
          rw [mul_comm _ D.host.AAbar, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
      _ ≤ D.host.AAbar⁻¹ * (D.host.AA * D.host.AAbar) := CovariantClass.elim D.host.AAbar⁻¹ hle
      _ = D.host.AA := by rw [mul_comm D.host.AA, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
  exact hle2 (FractionalIdeal.mem_spanSingleton_self _ _)

theorem form_smul (T : HSp D) (e : D.host.E) (t y : Fin T.rank → D.host.E) :
    ∑ c, ∑ d, star (t c) * T.gram c d * (e • y) d = e * ∑ c, ∑ d, star (t c) * T.gram c d * y d := by
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem genMap_mulVec (S T : HSp D) (a : D.host.E) (s' s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    genMap S T a s' t *ᵥ s = (a * ∑ c, ∑ d, star (s' c) * S.gram c d * s d) • t := by
  funext i
  rw [Finset.sum_comm]
  simp only [genMap, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hRat_add_left (S T : HSp D) (x x' y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T (x + x') y = hRat S T x y + hRat S T x' y := by
  simp only [hRat, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hRat_add_right (S T : HSp D) (x y y' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T x (y + y') = hRat S T x y + hRat S T x y' := by
  simp only [hRat, Matrix.add_apply, star_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hRat_neg_left (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T (-x) y = -hRat S T x y := by
  simp only [hRat, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hRat_neg_right (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T x (-y) = -hRat S T x y := by
  simp only [hRat, Matrix.neg_apply, star_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem hRat_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {ρ ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hρ : ρ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)))
    (hℓ : ℓ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))) :
    hRat S T ρ ℓ ∈ NAA D := by
  induction hρ using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a', ha', s', hs', t', ht', rfl⟩ := hw
    induction hℓ using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨p, hp⟩ := (hS.2 s).1 hs s' hs'
      obtain ⟨q, hq⟩ := (hT.2 t').1 ht' t ht
      rw [hRat_genMap, genMap_mulVec, form_smul, ← hp, ← hq]
      have hs : star a = D.host.conj a := bridge_star_holds D.R D.host a
      have e : star a * (a' * (p : D.host.E) * (q : D.host.E)) = (p * q) • (a' * D.host.conj a) := by
        rw [hs, Algebra.smul_def, map_mul]
        change _ = (p : D.host.E) * (q : D.host.E) * _
        ring
      rw [e]
      exact Submodule.smul_mem _ _ (FractionalIdeal.mul_mem_mul ha' (conj_mem_AAbar D ha))
    | zero => simp [hRat]
    | add x y _ _ hx hy => rw [hRat_add_right]; exact add_mem hx hy
    | neg x _ hx => rw [hRat_neg_right]; exact neg_mem hx
  | zero => simp [hRat]
  | add x y _ _ hx hy => rw [hRat_add_left]; exact add_mem hx hy
  | neg x _ hx => rw [hRat_neg_left]; exact neg_mem hx

end GlobalTheory.LatVac.RatDual

namespace GlobalTheory.LatVac

open RatDual Formalism.L2.Pj

theorem latRat_selfDual : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ (n : ℕ) (s s' : Fin n → Fin S.rank → D.host.E), (∀ i, s i ∈ ΛS ∧ s' i ∈ ΛS) ∧ ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0) → ∀ ρ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ρ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) ↔ ∀ ℓ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)), ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * hRat S T ρ ℓ) = n := by
  intro D S T ΛS ΛT hS hT ⟨n, s, s', hss, hdual⟩ ρ
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hAA := AA_ne_zero hP D
  refine ⟨fun hρ ℓ hℓ => trace_int_of_mem hP D (hRat_mem S T ΛS ΛT hS hT hρ hℓ), fun h => ?_⟩
  have h5 : ∀ v ∈ ΛS, ∀ t ∈ ΛT, ∑ c, ∑ d, star (t c) * T.gram c d * (ρ *ᵥ v) d ∈ D.host.AA := by
    intro v hv t ht
    refine mem_AA_of_trace D _ fun a ha => ?_
    rw [← hRat_genMap]
    exact h _ (AddSubgroup.subset_closure ⟨a, ha, v, hv, t, ht, rfl⟩)
  have h6 : ∀ v ∈ ΛS, ∀ b ∈ D.host.AA⁻¹, b • (ρ *ᵥ v) ∈ ΛT := by
    intro v hv b hb
    refine (hT.2 _).2 fun t ht => ?_
    rw [form_smul]
    have := FractionalIdeal.mul_mem_mul hb (h5 v hv t ht)
    rw [inv_mul_cancel₀ hAA, FractionalIdeal.mem_one_iff] at this
    exact this
  have h7 : ∀ v ∈ ΛS, ∀ v' ∈ ΛS, ∀ e ∈ D.host.AA * D.host.AA⁻¹, genMap S T e v' (ρ *ᵥ v) ∈
      latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
    intro v hv v' hv' e he
    refine FractionalIdeal.mul_induction_on (C := fun e => genMap S T e v' (ρ *ᵥ v) ∈
      latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))) he
      (fun a ha c hc => ?_) (fun u w hu hw => ?_)
    · refine AddSubgroup.subset_closure ⟨a, ha, v', hv', c • (ρ *ᵥ v), h6 v hv c hc, ?_⟩
      ext i j
      simp only [genMap, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    · have e : genMap S T (u + w) v' (ρ *ᵥ v) = genMap S T u v' (ρ *ᵥ v) + genMap S T w v' (ρ *ᵥ v) := by
        ext i j
        simp only [genMap, Matrix.of_apply, Matrix.add_apply, add_mul]
      show genMap S T (u + w) v' (ρ *ᵥ v) ∈ _
      rw [e]
      exact add_mem hu hw
  have e : ρ = ∑ i, genMap S T 1 (s' i) (ρ *ᵥ s i) := by
    refine Matrix.ext fun a j => ?_
    have h8 : ρ a j = ∑ b, ρ a b * ∑ i, s i b * ∑ k, star (s' i k) * S.gram k j := by
      simp only [hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h8, Matrix.sum_apply]
    simp only [genMap, Matrix.of_apply, one_mul, Matrix.mulVec, dotProduct]
    simp only [Finset.mul_sum (s := Finset.univ (α := Fin n))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← mul_assoc]
    exact (Finset.sum_mul _ _ _).symm
  rw [e]
  exact sum_mem fun i _ => h7 _ (hss i).1 _ (hss i).2 1
    (by rw [mul_inv_cancel₀ hAA]; exact FractionalIdeal.one_mem_one _)

end GlobalTheory.LatVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitScalar

open GlobalTheory.LatVac GlobalTheory.DualPairCheck

variable {D : D7}

theorem gramInv_star (S : HSp D) (i j : Fin S.rank) : star (S.gram⁻¹ i j) = S.gram⁻¹ j i := by
  have h : S.gramᴴ = S.gram := Matrix.ext fun i j => GlobalTheory.LatVac.gram_star S j i
  have h2 : (S.gram⁻¹)ᴴ = S.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, h]
  exact congrFun (congrFun h2 j) i

theorem hO_herm (S T : HSp D) (x y : WO S T) : cA D (hO S T x y) = hO S T y x := by
  unfold hO
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, RingHom.map_mul, cA_incA, GlobalTheory.DualPairCheck.cA_cA, gramInv_star, GlobalTheory.LatVac.gram_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem symplO_skew (S T : HSp D) (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  unfold symplO
  rw [← trace_cA, RingHom.map_mul, cA_incA, star_purely_imaginary_eq_neg, hO_herm, RingHom.map_neg, neg_mul, map_neg]

theorem hO_smul_left (S T : HSp D) (a : AE D) (x y : WO S T) : hO S T (a • x) y = a * hO S T x y := by
  simp only [hO, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem hO_smul_right (S T : HSp D) (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  simp only [hO, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem symplO_smul (S T : HSp D) (a : AE D) (x y : WO S T) :
    symplO S T (a • x) y = symplO S T x (cA D a • y) := by
  rw [symplO, symplO, hO_smul_left, hO_smul_right, GlobalTheory.DualPairCheck.cA_cA]

theorem symplO_zero_left (S T : HSp D) (y : WO S T) : symplO S T 0 y = 0 := by
  rw [← symplHom_apply, map_zero]; rfl

theorem symplO_zero_right (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  rw [← symplHom_apply, map_zero]

theorem symplO_sub_left (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x - x') y = symplO S T x y - symplO S T x' y := by
  rw [← symplHom_apply, map_sub]; rfl

theorem isHalf_iff {m n : ℕ} (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem symplO_eq_zero (S T : HSp D) {a b : AE D} (hab : cA D a * b = 0) {x y : WO S T} (hx : IsHalf a x)
    (hy : IsHalf b y) : symplO S T x y = 0 := by
  rw [← (isHalf_iff _ _).1 hx, ← (isHalf_iff _ _).1 hy, symplO_smul, smul_smul, hab, zero_smul, symplO_zero_right]

theorem symplOH_add_left (S T : HSp D) (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  simp only [symplOH, symplO_add_left, mul_add]

theorem symplOH_add_right (S T : HSp D) (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  simp only [symplOH, symplO_add_right, mul_add]

theorem symplOH_add_self (S T : HSp D) (x y : WO S T) :
    symplOH S T x y + symplOH S T x y = symplO S T x y := by
  rw [symplOH, ← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem symplOH_skew (S T : HSp D) (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  rw [symplOH, symplOH, symplO_skew, mul_neg]

theorem heisO_heisO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w w' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (heisO ψ S T w' f) = ψ (symplOH S T w w') • heisO ψ S T (w + w') f := by
  funext u
  simp only [heisO, Pi.smul_apply, smul_eq_mul, symplOH_add_left, symplOH_add_right, AddChar.map_add_eq_mul,
    add_assoc]
  ring

theorem heisO_add_of_orth (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {w w' : WO S T} (h : symplO S T w w' = 0)
    (f : WO S T → ℂ) : heisO ψ S T (w + w') f = heisO ψ S T w (heisO ψ S T w' f) := by
  rw [heisO_heisO, symplOH, h, mul_zero, AddChar.map_zero_eq_one, one_smul]

theorem heisO_comm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w w' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (heisO ψ S T w' f) = ψ (symplO S T w w') • heisO ψ S T w' (heisO ψ S T w f) := by
  rw [heisO_heisO, heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, add_comm w' w, ← symplOH_add_self,
    symplOH_skew S T w w', add_neg_cancel_right]

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext u
  simp only [heisO, symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]

def heisL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) : Module.End ℂ (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by funext u; simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by funext u; simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem heisL_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisL ψ S T w f = heisO ψ S T w f := rfl

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := (heisL ψ S T w).map_smul c f

theorem heisO_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) {ι : Type} (s : Finset ι)
    (f : ι → WO S T → ℂ) : heisO ψ S T w (∑ i ∈ s, f i) = ∑ i ∈ s, heisO ψ S T w (f i) :=
  map_sum (heisL ψ S T w) f s

def realIdem (D : D7) : AE D := pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E)

theorem cA_realIdem : cA D (realIdem D) = realIdem D := by
  show pairA D.host.F 1 0 ⊗ₜ[D.host.F] D.sp.cm.sig (1 : D.host.E) = _
  rw [map_one]; rfl

theorem infPart_realIdem : infPart D (realIdem D) = 1 := rfl

theorem finPart_realIdem : finPart D (realIdem D) = 0 := TensorProduct.zero_tmul _ _

theorem adele_ext {a b : AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) : a = b :=
  sub_eq_zero.1 (GlobalTheory.FockCompare.RealChart.adele_tensor_ext (a - b)
    (show infPart D (a - b) = 0 by rw [RingHom.map_sub, h1, sub_self])
    (show finPart D (a - b) = 0 by rw [RingHom.map_sub, h2, sub_self]))

theorem realIdem_mul_of_fin {a : AE D} (h : infPart D a = 0) : realIdem D * a = 0 :=
  adele_ext (by rw [RingHom.map_mul, h, mul_zero, RingHom.map_zero])
    (by rw [RingHom.map_mul, finPart_realIdem, zero_mul, RingHom.map_zero])

theorem realIdem_mul_of_real {a : AE D} (h : finPart D a = 0) : realIdem D * a = a :=
  adele_ext (by rw [RingHom.map_mul, infPart_realIdem, one_mul])
    (by rw [RingHom.map_mul, h, mul_zero])

theorem symplO_real_fin (S T : HSp D) {x y : WO S T} (hx : x.map (finPart D) = 0) (hy : y.map (infPart D) = 0) :
    symplO S T x y = 0 := by
  have h1 : realIdem D • x = x := Matrix.ext fun i j => realIdem_mul_of_real (congrFun (congrFun hx i) j)
  have h2 : realIdem D • y = 0 := Matrix.ext fun i j => realIdem_mul_of_fin (congrFun (congrFun hy i) j)
  rw [← h1, symplO_smul, cA_realIdem, h2, symplO_zero_right]

theorem latO_fin {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) : u.map (infPart D) = 0 := by
  refine latO_induction (p := fun u => u.map (infPart D) = 0) (fun α _ M _ => ?_) ?_ (fun x y hx hy => ?_)
    (fun x hx => ?_) hu
  · ext i j
    exact TensorProduct.zero_tmul _ _
  · ext i j
    exact (infPart D).map_zero
  · ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
    show infPart D (x i j + y i j) = 0
    rw [RingHom.map_add (f := _), h1, h2, add_zero]
  · ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    show infPart D (-x i j) = 0
    rw [RingHom.map_neg, h1, neg_zero]

theorem isSplitIdem_conj {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, h3, h4⟩ := he
  refine ⟨by rw [← RingHom.map_mul, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2], v, ε, h3, ?_⟩
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h4]

theorem infPart_splitIdem {e : AE D} (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h4⟩ := he
  have h5 : infPart D (e + cA D e) = 0 := by
    rw [h4]
    exact TensorProduct.zero_tmul _ _
  have h6 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
  rw [h6, RingHom.map_mul, h5, mul_zero]

theorem half_fin {m n : ℕ} {e : AE D} (he : IsSplitIdem D e) {u : Mx D m n} (hu : IsHalf e u) :
    u.map (infPart D) = 0 := by
  ext i j
  show infPart D (u i j) = 0
  rw [← hu i j, RingHom.map_mul, infPart_splitIdem he, zero_mul]

theorem continuous_symplO (S T : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WO S T} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplO S T (x t) (y t) := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hy' : ∀ i j, Continuous fun t => cA D (y t i j) := fun i j =>
    GlobalTheory.FockCompare.ThetaCont.continuous_conj.comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hx' : ∀ i j, Continuous fun t => x t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hx)
  refine ht.comp (continuous_const.mul ?_)
  exact continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul (hx' _ _)

theorem exists_nsmul_mem {m n : ℕ} (U : AddSubgroup (Mx D m n)) (hU : IsOpen (U : Set (Mx D m n))) {y : Mx D m n}
    (hy : y.map (infPart D) = 0) : ∃ N : ℕ, 0 < N ∧ N • y ∈ U := by
  let φ : Af D.host.F → Mx D m n := fun α => Matrix.of fun i j => pairA D.host.F 0 α • y i j
  have hp : Continuous fun α : Af D.host.F => pairA D.host.F 0 α := continuous_const.prodMk continuous_id
  have hφ : Continuous φ := continuous_pi fun i => continuous_pi fun j => hp.smul continuous_const
  have h0 : φ 0 = 0 := Matrix.ext fun i j => zero_smul (AF D.host.F) (y i j)
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele D.host.F (φ ⁻¹' U)
    (hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds (h0 ▸ U.zero_mem)))
  refine ⟨N, hN, ?_⟩
  have h1 : φ (N • 1) ∈ U := h 1 fun v => one_mem _
  have h2 : φ (N • 1) = N • y := by
    refine Matrix.ext fun i j => ?_
    have e1 : pairA D.host.F 0 (N • 1) = N • (1 - pairA D.host.F 1 0) :=
      Prod.ext (show (0 : Ainf D.host.F) = N • (1 - 1) by rw [sub_self, smul_zero])
        (show (N • 1 : Af D.host.F) = N • (1 - 0) by rw [sub_zero])
    have e2 : pairA D.host.F 1 0 • y i j = 0 := by
      rw [Algebra.smul_def]
      exact realIdem_mul_of_fin (congrFun (congrFun hy i) j)
    show pairA D.host.F 0 (N • 1) • y i j = N • y i j
    rw [e1, smul_assoc, sub_smul, one_smul, e2, sub_zero]
  rwa [h2] at h1

end GlobalTheory.SplitScalar

end
end

