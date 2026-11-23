module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0069
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0418
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSplitProdRight

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicInnerDoubleCosetOpAdjoint
section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory
namespace DoubleCosetAdjoint

variable {G : Type} [Group G]

def Rel (J L : Subgroup G) (x : G) (u v : G ⧸ J) : Prop :=
  ∃ h a : G, a ∈ L ∧ (∃ k₁ k₂ : J, a = (k₁ : G) * x * k₂) ∧ u = (h : G ⧸ J) ∧ v = ((h * a : G) : G ⧸ J)

theorem Rel.symm {J L : Subgroup G} {x : G} {u v : G ⧸ J} (h : Rel J L x u v) : Rel J L x⁻¹ v u := by
  obtain ⟨h, a, ha, ⟨k₁, k₂, hk⟩, rfl, rfl⟩ := h
  refine ⟨h * a, a⁻¹, L.inv_mem ha, ⟨k₂⁻¹, k₁⁻¹, ?_⟩, rfl, by simp⟩
  rw [hk]; simp [mul_assoc]

theorem rel_iff {J L : Subgroup G} {x : G} {A : Finset G} (hL : ∀ a ∈ A, a ∈ L) (hA : IsDC J x A)
    (y : G) (v : G ⧸ J) : Rel J L x (y : G ⧸ J) v ↔ ∃ a ∈ A, v = ((y * a : G) : G ⧸ J) := by
  constructor
  · rintro ⟨h, b, -, ⟨k₁, k₂, hk⟩, hy, rfl⟩
    have hy' : y⁻¹ * h ∈ J := QuotientGroup.eq.1 hy
    obtain ⟨a, ⟨ha, ha'⟩, -⟩ := hA.2 (y⁻¹ * h * b) ⟨⟨_, hy'⟩ * k₁, k₂, by rw [hk]; simp [mul_assoc]⟩
    refine ⟨a, ha, (QuotientGroup.eq.2 ?_).symm⟩
    simpa [mul_assoc] using ha'
  · rintro ⟨a, ha, rfl⟩
    exact ⟨y, a, hL a ha, hA.1 a ha, rfl, rfl⟩

theorem injOn_coset {J : Subgroup G} {x : G} {A : Finset G} (hA : IsDC J x A) (y : G) :
    Set.InjOn (fun a : G => ((y * a : G) : G ⧸ J)) (A : Set G) := by
  intro a ha a' ha' h
  have h' : (y * a)⁻¹ * (y * a') ∈ J := QuotientGroup.eq.1 h
  have h'' : a⁻¹ * a' ∈ J := by simpa [mul_assoc] using h'
  exact (hA.2 a' (hA.1 a' ha')).unique ⟨ha, h''⟩ ⟨ha', by simp⟩

theorem char_eq {J L : Subgroup G} (χ : J →* ℂˣ)
    (hd : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) {a b : G} (ha : a ∈ L) (hb : b ∈ L) (k k' : J)
    (h : (k : G) * b = a * k') : χ k = χ k' := by
  obtain ⟨k₁, h₁, k₂, h₂, hL, hk, hc⟩ := hd k k.2
  obtain ⟨m₁, g₁, m₂, g₂, gL, gk, -⟩ := hd k' k'.2
  have e1 : k = ⟨k₁, h₁⟩ * ⟨k₂, h₂⟩ := Subtype.ext hk
  have e2 : k' = ⟨m₁, g₁⟩ * ⟨m₂, g₂⟩ := Subtype.ext gk
  have e3 : k₂ * m₂⁻¹ = (k₁ * b)⁻¹ * (a * m₁) := by
    rw [hk, gk, mul_assoc, (hc b hb).eq] at h
    have : k₂ = (k₁ * b)⁻¹ * (a * (m₁ * m₂)) := by rw [← h]; group
    rw [this]; group
  have e4 : χ (⟨k₂, h₂⟩ * ⟨m₂, g₂⟩⁻¹) = 1 := hχ _ (by
    show k₂ * m₂⁻¹ ∈ L
    rw [e3]; exact L.mul_mem (L.inv_mem (L.mul_mem hL hb)) (L.mul_mem ha gL))
  rw [map_mul, map_inv, mul_inv_eq_one] at e4
  rw [e1, e2, map_mul, map_mul, hχ ⟨k₁, h₁⟩ hL, hχ ⟨m₁, g₁⟩ gL, e4]

theorem exists_pairing {Γ W : Type} [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) {J L : Subgroup G} (χ : J →* ℂˣ) (x : G)
    (hn : ∀ k, ‖(χ k : ℂ)‖ = 1)
    (hd : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ)
    (hF' : F' ∈ AdForms ι ρ J χ) :
    ∃ φ : (G ⧸ J) × (G ⧸ J) → ℂ, ∀ h a : G, a ∈ L → (∃ k₁ k₂ : J, a = (k₁ : G) * x * k₂) →
      φ ((h : G ⧸ J), ((h * a : G) : G ⧸ J)) = inner ℂ (F (h * a)) (F' h) := by
  classical
  refine ⟨fun z => if H : Rel J L x z.1 z.2 then
    inner ℂ (F (H.choose * H.choose_spec.choose)) (F' H.choose) else 0, ?_⟩
  intro h a ha hx
  have H : Rel J L x (h : G ⧸ J) ((h * a : G) : G ⧸ J) := ⟨h, a, ha, hx, rfl, rfl⟩
  simp only [dif_pos H]
  obtain ⟨hb, -, e1, e2⟩ := H.choose_spec.choose_spec
  generalize H.choose_spec.choose = b at hb e2 ⊢
  generalize H.choose = g at e1 e2 ⊢
  have f1 : h⁻¹ * g ∈ J := QuotientGroup.eq.1 e1
  have f2 : (h * a)⁻¹ * (g * b) ∈ J := QuotientGroup.eq.1 e2
  have c := char_eq χ hd hχ ha hb ⟨_, f1⟩ ⟨_, f2⟩ (by simp [mul_assoc])
  have u1 := hF 1 (h * a) ⟨_, f2⟩
  have u2 := hF' 1 h ⟨_, f1⟩
  simp only [map_one, one_mul, mul_inv_cancel_left, Module.End.one_apply] at u1 u2
  rw [u1, u2, c, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hn]
  simp

omit [Group G] in
theorem finsum_fibre {Q : Type} {P : Q → Prop} (s : Set {z // P z}) (A : Finset G) (m : G → Q)
    (hm : Set.InjOn m (A : Set G)) (hs : Subtype.val '' s = m '' (A : Set G)) (φ : Q → ℂ) :
    s.Finite ∧ ∑ᶠ z ∈ s, φ z.1 = ∑ a ∈ A, φ (m a) := by
  constructor
  · refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    rw [hs]; exact A.finite_toSet.image _
  · rw [← finsum_mem_image Subtype.val_injective.injOn, hs, finsum_mem_image hm,
      finsum_mem_coe_finset]

end DoubleCosetAdjoint


open DoubleCosetAdjoint in
theorem adInner_dcOp_adjoint : ∀ {G Γ W I : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Fintype I] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J L : Subgroup G) (χ : J →* ℂˣ) (y : I → G) (x : G) (A A' : Finset G), (∀ γ u u', inner ℂ (ρ γ u) (ρ γ u') = inner ℂ u u') → (∀ k, ‖(χ k : ℂ)‖ = 1) → IsReps ι J y → (∀ i, Finite (stab ι J (y i))) → (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J x⁻¹ A' → ∀ F ∈ AdForms ι ρ J χ, ∀ F' ∈ AdForms ι ρ J χ, adInner ι J y (dcOp A F) F' = adInner ι J y F (dcOp A' F') := by
  intro G Γ W I _ _ _ _ _ ι ρ J L χ y x A A' hρ hn hy hfin hd hχ hA hA' hD hD' F hF F' hF'
  obtain ⟨φ, hφ⟩ := exists_pairing ι ρ χ x hn hd hχ hF hF'
  letI : MulAction Γ (G ⧸ J) := MulAction.compHom (G ⧸ J) ι
  have hs : ∀ (γ : Γ) (g : G), γ • (g : G ⧸ J) = ((ι γ * g : G) : G ⧸ J) := fun _ _ => rfl
  let S : SubMulAction Γ ((G ⧸ J) × (G ⧸ J)) :=
    { carrier := {z | Rel J L x z.1 z.2}
      smul_mem' := by
        rintro γ ⟨u, v⟩ ⟨h, a, ha, hx, e1, e2⟩
        refine ⟨ι γ * h, a, ha, hx, ?_, ?_⟩
        · show γ • u = _
          rw [show u = _ from e1, hs]
        · show γ • v = _
          rw [show v = _ from e2, hs, mul_assoc] }
  have hst : ∀ g : G, MulAction.stabilizer Γ (g : G ⧸ J) = stab ι J g := by
    intro g
    ext γ
    rw [MulAction.mem_stabilizer_iff, hs, eq_comm, QuotientGroup.eq, mem_stab, mul_assoc]
  have horb : ∀ u : G ⧸ J, ∃! i, u ∈ MulAction.orbit Γ ((y i : G) : G ⧸ J) := by
    intro u
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective u
    refine (existsUnique_congr fun i => ?_).1 (hy h)
    constructor
    · rintro ⟨γ, k, rfl⟩
      exact ⟨γ, by simp only [hs]; exact (QuotientGroup.mk_mul_of_mem _ k.2).symm⟩
    · rintro ⟨γ, hγ⟩
      simp only [hs] at hγ
      exact ⟨γ, ⟨_, QuotientGroup.eq.1 hγ⟩, by simp only [mul_inv_cancel_left]⟩
  have hf : ∀ i, Finite (MulAction.stabilizer Γ ((y i : G) : G ⧸ J)) := fun i => by
    rw [hst]; exact hfin i
  have h1 := fun g : G => finsum_fibre (P := fun z => z ∈ S) {z | z.1.1 = (g : G ⧸ J)} A
    (fun a => ((g : G ⧸ J), ((g * a : G) : G ⧸ J)))
    (fun a ha a' ha' h => injOn_coset hD g ha ha' (congrArg Prod.snd h)) (by
      ext ⟨u, v⟩
      constructor
      · rintro ⟨⟨z, hz⟩, hz', rfl⟩
        obtain rfl : u = _ := hz'
        obtain ⟨a, ha, e⟩ := (rel_iff hA hD g v).1 hz
        exact ⟨a, ha, by rw [e]⟩
      · rintro ⟨a, ha, e⟩
        exact ⟨⟨(_, _), (rel_iff hA hD g _).2 ⟨a, ha, rfl⟩⟩, rfl, e⟩) φ
  have h2 := fun g : G => finsum_fibre (P := fun z => z ∈ S) {z | z.1.2 = (g : G ⧸ J)} A'
    (fun a => (((g * a : G) : G ⧸ J), (g : G ⧸ J)))
    (fun a ha a' ha' h => injOn_coset hD' g ha ha' (congrArg Prod.fst h)) (by
      ext ⟨u, v⟩
      constructor
      · rintro ⟨⟨z, hz⟩, hz', rfl⟩
        obtain rfl : v = _ := hz'
        obtain ⟨a, ha, e⟩ := (rel_iff hA' hD' g u).1 (Rel.symm hz)
        exact ⟨a, ha, by rw [e]⟩
      · rintro ⟨a, ha, e⟩
        have := ((rel_iff hA' hD' g _).2 ⟨a, ha, rfl⟩).symm
        rw [inv_inv] at this
        exact ⟨⟨(_, _), this⟩, rfl, e⟩) φ
  have key := weighted_fibre_sums_eq (Γ := Γ) (Z := S) (fun z => z.1.1) (fun z => z.1.2)
    (fun i => ((y i : G) : G ⧸ J)) (fun i => ((y i : G) : G ⧸ J)) (fun z => φ z.1)
    (fun _ _ => rfl) (fun _ _ => rfl) horb horb hf hf (fun i => (h1 _).1) (fun i => (h2 _).1) (by
      rintro γ ⟨⟨u, v⟩, h, a, ha, hx, e1, e2⟩
      obtain rfl : u = _ := e1
      obtain rfl : v = _ := e2
      show φ (γ • (h : G ⧸ J), γ • ((h * a : G) : G ⧸ J)) = φ (_, _)
      rw [hs, hs, ← mul_assoc, hφ _ a ha hx, hφ _ a ha hx]
      have u1 := hF γ (h * a) 1
      have u2 := hF' γ h 1
      simp only [map_one, OneMemClass.coe_one, mul_one, Units.val_one, one_smul] at u1 u2
      rw [mul_assoc, u1, u2, hρ])
  simp only [(h1 _).2, (h2 _).2, hst] at key
  unfold adInner dcOp
  convert key using 3 with i _ i _
  · rw [sum_inner]
    exact Finset.sum_congr rfl fun a ha => (hφ _ a (hA a ha) (hD.1 a ha)).symm
  · rw [inner_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨k₁, k₂, hk⟩ := hD'.1 a ha
    have := hφ (y i * a) a⁻¹ (L.inv_mem (hA' a ha)) ⟨k₂⁻¹, k₁⁻¹, by rw [hk]; simp [mul_assoc]⟩
    rw [mul_inv_cancel_right] at this
    exact this.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyFactorizationSemisimple
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.SSComplement

section Rep

variable {Γ k : Type} [Group Γ] [Field k]

def blockM {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k) (ρ₂ : Γ →* GL (Fin b) k) :
    Γ →* Matrix (Fin n) (Fin n) k where
  toFun g := Matrix.reindex e0 e0
    (Matrix.fromBlocks (ρ₁ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ₂ g : Matrix (Fin b) (Fin b) k))
  map_one' := by simp
  map_mul' g g' := by simp [Matrix.fromBlocks_multiply]

def diagM {t : ℕ} (χ : Fin t → Γ →* kˣ) : Γ →* Matrix (Fin t) (Fin t) k where
  toFun g := Matrix.diagonal fun c => ((χ c g : kˣ) : k)
  map_one' := by simp
  map_mul' g h := by simp [Matrix.diagonal_mul_diagonal]

theorem blockM_ss {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k)
    (ρ₂ : Γ →* GL (Fin b) k) (h₁ : IsSSRep ρ₁) (h₂ : IsSSRep ρ₂) : IsSSRep (blockM e0 ρ₁ ρ₂).toHomUnits := by
  refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod ((LinearEquiv.funCongrLeft k k e0).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) h₁ h₂
  show _ = _
  ext i <;> simp [blockM, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl

theorem ss_of_scalar {a : ℕ} (ρ : Γ →* GL (Fin a) k) (c : Γ → k)
    (h : ∀ g v, (ρ g : Matrix (Fin a) (Fin a) k).mulVec v = c g • v) : IsSSRep ρ := by
  intro W _
  obtain ⟨W', hW'⟩ := W.exists_isCompl
  exact ⟨W', fun g v hv => by rw [h]; exact W'.smul_mem _ hv, hW'⟩

theorem diagM_ss : ∀ {t : ℕ} (χ : Fin t → Γ →* kˣ), IsSSRep (diagM χ).toHomUnits := by
  intro t
  induction t with
  | zero =>
    intro χ
    exact ss_of_scalar _ (fun _ => 0) fun g v => funext fun c => c.elim0
  | succ t ih =>
    intro χ
    refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod (ρ₁ := (diagM fun c : Fin t => χ (Fin.castAdd 1 c)).toHomUnits)
      (ρ₂ := (diagM fun c : Fin 1 => χ (Fin.natAdd t c)).toHomUnits)
      ((LinearEquiv.funCongrLeft k k finSumFinEquiv).trans
        (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) (ih _)
      (ss_of_scalar _ (fun g => ((χ (Fin.last t) g : kˣ) : k)) fun g v => ?_)
    · show _ = _
      ext i <;> simp [diagM, Matrix.mulVec_diagonal, LinearMap.funLeft]
    · funext c
      obtain rfl : c = 0 := Subsingleton.elim _ _
      change (Matrix.diagonal fun c : Fin 1 => ((χ (Fin.natAdd t c) g : kˣ) : k)).mulVec v 0 = _
      exact Matrix.mulVec_diagonal _ _ _

end Rep

end GlobalTheory.SSComplement
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfData
section
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.CoeffEmbedding

theorem continuous_iotaOQ_of_data : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    (N : NData R H what₂) (A : NAut N) (i : N.Loc), Continuous (iotaOQ N A i) :=
  fun {R H what₂} N A i => continuous_iotaOQ R H what₂ N A i

end GlobalTheory.CoeffEmbedding
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExcessMemIcc
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ExcessLow

theorem excess_sum (f : ℕ → ℝ) (k M : ℕ) (w N S η W : ℝ) (hk : 2 ≤ k) (hN1 : 1 ≤ N) (hS : 0 ≤ S)
    (hlong : ∀ r < k, w - N - 1 / 2 < f r ∧ f r < w + (if r = 0 then 3 * S else S))
    (hblock : ∀ r, k ≤ r → r < k + M → 0 ≤ f r ∧ f r ≤ η)
    (hkN : (k : ℝ) * N ≤ S / 4) (hkS : (k : ℝ) * S ≤ W) (hM : (M : ℝ) * η ≤ W) (hW : W ≤ w) :
    0 ≤ ∑ r ∈ Finset.range (k + M), f r - ((k : ℝ) - 1) * w ∧
      ∑ r ∈ Finset.range (k + M), f r - ((k : ℝ) - 1) * w ≤ 4 * w := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Finset.sum_range_add]
  have b0 : 0 ≤ ∑ r ∈ Finset.range M, f (k + r) :=
    Finset.sum_nonneg fun r hr =>
      (hblock _ (by omega) (by have := Finset.mem_range.1 hr; omega)).1
  have b1 : ∑ r ∈ Finset.range M, f (k + r) ≤ M * η := by
    have := Finset.sum_le_card_nsmul (Finset.range M) (fun r => f (k + r)) η fun r hr =>
      (hblock _ (by omega) (by have := Finset.mem_range.1 hr; omega)).2
    simpa using this
  have l0 : (k : ℝ) * (w - N - 1 / 2) ≤ ∑ r ∈ Finset.range k, f r := by
    have := Finset.card_nsmul_le_sum (Finset.range k) f (w - N - 1 / 2) fun r hr =>
      (hlong r (Finset.mem_range.1 hr)).1.le
    simpa only [Finset.card_range, nsmul_eq_mul] using this
  have l1 : ∑ r ∈ Finset.range k, f r ≤ k * (w + S) + 2 * S := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have h0 := (hlong 0 (by omega)).2
    rw [if_pos rfl] at h0
    have h1 := Finset.sum_le_card_nsmul (Finset.range k') (fun r => f (r + 1)) (w + S) fun r hr => by
      have := (hlong (r + 1) (by have := Finset.mem_range.1 hr; omega)).2
      rw [if_neg (by omega)] at this
      exact this.le
    simp only [Finset.card_range, nsmul_eq_mul] at h1
    push_cast
    nlinarith
  have h2S : 2 * S ≤ k * S := mul_le_mul_of_nonneg_right hk' hS
  have hkN1 : (k : ℝ) ≤ k * N := le_mul_of_one_le_right (by linarith) hN1
  constructor
  · nlinarith
  · nlinarith

theorem excess_mem_Icc : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ¬ IsTopPl (Fm.D x i) z → 0 ≤ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z ∧ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z ≤ 4 * wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.LongRows.longRows Fm
  obtain ⟨x4, h4⟩ := GlobalTheory.blockRows_mem_Icc Fm
  refine ⟨max (max x1 x2) (max x3 x4), fun x hx hx1 i u j hj z hz => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hx
  obtain ⟨a1, a2, a3, -⟩ := h1 x e1 hx1 i
  have hk := (Fm.D x i).R.m_add_three_le_k
  rw [GlobalTheory.nuD_card_eq_sum_nuRow (Fm.D x i) (nuRowOK _) u j hj z]
  have heta := (Fm.L x i).etaSz_pos
  refine excess_sum _ (Fm.D x i).R.k (j * ((Fm.D x i).R.t + 1)) _
    ((Fm.D x i).R.N (Fm.D x i).R.m) (Fm.L x i).Sc (Fm.L x i).etaSz
    ((Fm.L x i).sc.w'' (Fm.D x i).R.n) (by omega) ?_ (Fm.L x i).Sc_pos.le
    (fun r hr => (h3 x e3 hx1 i u j hj z r hr).1 hz)
    (fun r hr hr' => h4 x e4 hx1 i u j hj z r hr hr') a1 a2 ?_ (h2 x e2 hx1 i j hj z).1
  · have : 1 ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
      unfold Ranks.N
      omega
    exact_mod_cast this
  · refine le_trans ?_ a3
    apply mul_le_mul_of_nonneg_right _ heta.le
    push_cast
    have : (j : ℝ) ≤ (Fm.D x i).R.m := by exact_mod_cast hj.le
    exact mul_le_mul_of_nonneg_right this (by positivity)

end GlobalTheory.ExcessLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
section
noncomputable section

namespace GlobalTheory.HeckeSplitRow

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host

def HeckeCharTie {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) : Prop :=
  ∃ e : A.CG 1 → HChar H.E, Function.Injective e ∧
    (∀ π w, A.unr (A.locG π w) ↔ (e π).UnrAt w) ∧
    ∀ π w, (e π).UnrAt w → A.frobEig (A.locG π w) = {(((e π).val w)⁻¹ : ℂˣ).1}

theorem heckeCharTie_of_tied {D : D7} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch}
    (T : NCharTied D C nch Tp) : HeckeCharTie D.nd D.naut :=
  ⟨fun π => (T.e1 π).1, fun _ _ h => T.e1.injective (Subtype.ext h), T.unr_iff, T.frob⟩

theorem loc_eq_one {L : Type} [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L))
    (hu : χ.UnrAt v) (hv : χ.val v = 1) : χ.loc v = 1 := by
  ext x : 1
  set p := atFin v (unif v) with hp
  have hpv : Valued.v (p : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  have hx0 : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  set n : ℤ := WithZero.log (Valued.v (x : v.adicCompletion L)) with hn
  have hxn : Valued.v (x : v.adicCompletion L) = WithZero.exp n := (WithZero.exp_log hx0).symm
  have hunit : IsUnitAt v (x * p ^ n) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hpv, hxn, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h1 := hu _ hunit
  have hp1 : χ.loc v p = 1 := hv
  rw [map_mul, map_zpow, hp1, one_zpow, mul_one] at h1
  exact h1

theorem complexConj_eq {R : Ranks} (H : Host R) [IsCMField H.E] (z : H.E) :
    IsCMField.complexConj H.E z = H.conj z := by
  apply H.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  exact (H.toHostAx.conjE_apply H.φ₀ z).symm

theorem eq_one_of_split {R : Ranks} (H : Host R) (ν : HChar H.E)
    (h : ∀ᶠ w in Filter.cofinite, IsSplitPl H w → ν.UnrAt w ∧ ν.val w = 1) : ν = 1 := by
  have : IsCMField H.E := H.isCMField_hostE
  apply Subtype.ext
  refine _root_.GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne (maximalRealSubfield H.E) H.E ν.1 ν.2 ?_
  filter_upwards [h, _root_.GlobalTheory.HeckeSplit.eventually_degOne_moved (maximalRealSubfield H.E) H.E (IsCMField.complexConj H.E)
    (IsCMField.complexConj_ne_one H.E)] with w hw hs hd
  obtain ⟨x, hx, hy⟩ := hs hd
  have hsp : IsSplitPl H w := ⟨x, hx, fun y hyx => hy y (by rw [complexConj_eq]; exact hyx)⟩
  exact (GlobalTheory.HeckeSplit.trivAt_iff H.E ν w).2 (loc_eq_one ν w (hw hsp).1 (hw hsp).2)

theorem heckeCharEqOfSplit_of_tie : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N), HeckeCharTie N A → GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.HeckeCharEqOfSplit N A := by
  rintro R H what₂ N A ⟨e, hinj, hunr, hfrob⟩ χ χ' hag
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.agreeAtAlmostAllSplit_iff] at hag
  apply hinj
  rw [← mul_inv_eq_one]
  apply eq_one_of_split H
  filter_upwards [hag, A.locG_unr_ae χ, A.locG_unr_ae χ'] with w hw h1 h2 hs
  have u1 := (hunr χ w).1 h1
  have u2 := (hunr χ' w).1 h2
  refine ⟨fun x hx => ?_, ?_⟩
  · change (e χ).loc w x * ((e χ').loc w x)⁻¹ = 1
    rw [u1 x hx, u2 x hx, inv_one, mul_one]
  · have hf := hfrob χ w u1
    rw [hw hs, hfrob χ' w u2, Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
    rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]

theorem heckeSplitOne_of_tie {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) (h : HeckeCharTie N A) : GlobalTheory.ThetaExh.HeckeSplitOne N A := fun χ χ' hw =>
  heckeCharEqOfSplit_of_tie R H what₂ N A h χ χ' ((GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.agreeAtAlmostAllSplit_iff A χ χ').2 hw)

end GlobalTheory.HeckeSplitRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsDCOfMemDoubleCoset
section
namespace GlobalTheory.HkB

open Formalism.IndefR.Bridge

theorem isDC_of_mem_doubleCoset {G : Type} [Group G] {J : Subgroup G} {x x' : G} {A : Finset G}
    (hA : IsDC J x' A) (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂) : IsDC J x A := by
  obtain ⟨k₁, k₂, rfl⟩ := hx
  constructor
  · intro a ha
    obtain ⟨u, v, rfl⟩ := hA.1 a ha
    exact ⟨u * k₁, k₂ * v, by simp [mul_assoc]⟩
  · rintro _ ⟨u, v, rfl⟩
    exact hA.2 _ ⟨u * k₁⁻¹, k₂⁻¹ * v, by simp [mul_assoc]⟩

theorem dcOp_eq_and_level {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J L : Subgroup G) (χ : J →* ℂˣ) (x x' : G) (A A' : Finset G) (F : G → W)
    (hs : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) (hAL : ∀ a ∈ A, a ∈ L) (hAL' : ∀ a ∈ A', a ∈ L)
    (hA : IsDC J x A) (hA' : IsDC J x' A') (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂)
    (hF : ∀ (k : J) (h : G), F (h * k) = (χ k : ℂ) • F h) :
    dcOp A F = dcOp A' F ∧ (∀ (k : J) (h : G), (dcOp A F) (h * k) = (χ k : ℂ) • (dcOp A F) h) := by
  have hF' : F ∈ AdForms (1 : G →* G) (1 : G →* Module.End ℂ W) J χ := by
    intro γ h k
    simpa using hF k h
  refine ⟨dcOp_eq_of_isDC _ _ hχ hA (isDC_of_mem_doubleCoset hA' hx) hAL hAL' hF', fun k h => ?_⟩
  have h1 := LocSplit.dcOp_mem (1 : G →* G) (1 : G →* Module.End ℂ W) hs hχ hA hAL hF' 1 h k
  simpa using h1

end GlobalTheory.HkB
end

