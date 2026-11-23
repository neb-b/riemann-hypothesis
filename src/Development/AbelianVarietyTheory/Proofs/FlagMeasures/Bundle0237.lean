module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0234
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericLocalTermsSelfDualLattices
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0232

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFrames
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.TermOver

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

lemma mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ img g Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [img, Submodule.mem_map]

lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * k) Λ = img g (img k Λ) := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

lemma img_one (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma img_selfDual (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} (hΛ : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  obtain ⟨h1, h2, h3⟩ := hΛ
  refine ⟨h1.map _, ?_, ?_⟩
  · have himg : ((img g Λ : Submodule M.L.O V) : Set V) = (g : V →ₗ[E] V) '' (Λ : Set V) := by
      ext x
      simp only [SetLike.mem_coe, mem_img, Set.mem_image]
      rfl
    rw [himg, ← Submodule.map_span, h2, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr g.surjective
  · intro x
    constructor
    · intro hx y hy
      obtain ⟨a, ha, rfl⟩ := (mem_img g Λ x).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_img g Λ y).1 hy
      rw [hg]
      exact (h3 a).1 ha b hb
    · intro hx
      obtain ⟨a, rfl⟩ := g.surjective x
      refine (mem_img g Λ _).2 ⟨a, (h3 a).2 fun y hy => ?_, rfl⟩
      have := hx (g y) ((mem_img g Λ _).2 ⟨y, hy, rfl⟩)
      rwa [hg] at this

lemma img_frame (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} {r : ℕ} {f : Fin (r + 1) → V} {T : F} (hf : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun b => g (f b)) T := by
  obtain ⟨⟨p1, p2, p3⟩, h2, h3, h4, h5⟩ := hf
  refine ⟨⟨fun a => (mem_img g Λ _).2 ⟨f a, p1 a, rfl⟩, ?_, ?_⟩, ?_, ?_, h4, h5⟩
  · exact p2.map' (g : V →ₗ[E] V) (LinearEquiv.ker g)
  · intro x hx hs
    obtain ⟨y, hy, rfl⟩ := (mem_img g Λ x).1 hx
    have hrange : Set.range (fun b => g (f b)) = (g : V →ₗ[E] V) '' Set.range f := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span] at hs
    obtain ⟨y', hy', hyy⟩ := hs
    have hyy' : y' = y := g.injective hyy
    subst hyy'
    have hO := p3 y' hy hy'
    have hmap : ∀ v ∈ Submodule.span M.L.O (Set.range f),
        g v ∈ Submodule.span M.L.O (Set.range fun b => g (f b)) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨b, rfl⟩ := hv
        exact Submodule.subset_span ⟨b, rfl⟩
      | zero => simp
      | add a b _ _ ha hb =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have : g (c • a) = c • g a := by
          change g ((c : E) • a) = (c : E) • g a
          exact map_smul g (c : E) a
        rw [this]
        exact Submodule.smul_mem _ c ha
    exact hmap y' hO
  · intro a b hab
    rw [hg]
    exact h2 a b hab
  · rw [hg]
    exact h3

lemma side (hM : M.OK) (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) {Λ : Submodule M.L.O V}
    {f : Fin (r + 1) → V} (hΛ : H.IsSelfDual Λ) (hf : H.IsFrame Λ r f Fr.T) (hT : Tri E Fr.f f) :
    ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧
      ∃ n ∈ Fr.N, f = (fun b => n (Fr.f b)) ∧ Λ = img n (Fr.LamStd L) := by
  obtain ⟨h1, -, h3⟩ := _root_.GlobalTheory.LocOver.UnipOnto.unipotent_onto M hM H r Fr hf.2.2.2.2
  obtain ⟨n, hn, hnf⟩ := h3 f hT
  have hu : IsUnitary H n⁻¹ := ((h1 _).1 (Fr.N.inv_mem hn)).1
  have hfr : H.IsFrame (img n⁻¹ Λ) r Fr.f Fr.T := by
    have := img_frame H hu hf
    have he : (fun b => n⁻¹ (f b)) = Fr.f := by
      funext b
      rw [hnf]
      exact n.symm_apply_apply _
    rwa [he] at this
  obtain ⟨L, hL, -, n0, hn0, hfix, hΛ0⟩ :=
    _root_.GlobalTheory.StdLat.eq_img_lamStd M hM H r Fr (img n⁻¹ Λ) (img_selfDual H hu hΛ) hfr
  refine ⟨L, hL, n * n0, Fr.N.mul_mem hn hn0, ?_, ?_⟩
  · rw [hnf]
    funext b
    change n (Fr.f b) = n (n0 (Fr.f b))
    rw [hfix]
  · rw [img_mul, ← hΛ0, ← img_mul, mul_inv_cancel, img_one]

end

theorem exists_datum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (P : FPair H r) (t : Term V M r), H.IsTerm t → t.T = P.A.T → t.T' = P.B.T → Tri E P.A.f t.f → Tri E P.B.f t.f' → ∃ d : Datum P, IsTermOver P d t := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r P t ht hT hT' hf hf'
  obtain ⟨hsd, hfr, hfr', -, -, hg⟩ := ht
  rw [hT] at hfr
  rw [hT'] at hfr'
  obtain ⟨L, hL, n, hn, hnf, hnΛ⟩ := side hM H r P.A hsd hfr hf
  obtain ⟨L', hL', n', hn', hnf', hnΛ'⟩ := side hM H r P.B hsd hfr' hf'
  let s : Term V M r := ⟨t.abelian₂, P.A.f, P.B.f, t.T, t.T'⟩
  refine ⟨⟨L, L', hL, hL', {p | ∃ g, M.split = some g ∧ p ∈ H.iotaGraph g s}, ?_⟩, hT, hT',
    ⟨n, hn, hnf, hnΛ⟩, ⟨n', hn', hnf', hnΛ'⟩, ?_⟩
  · intro h
    ext p
    simp [h]
  · intro g hgs
    refine ⟨(hg g hgs).2.2, ?_⟩
    ext p
    constructor
    · intro hp
      exact ⟨g, hgs, hp⟩
    · rintro ⟨g', hg', hp⟩
      obtain rfl : g = g' := Option.some.inj (hgs.symm.trans hg')
      exact hp

end GlobalTheory.LocOver.TermOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsListProd
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.ProdChar

theorem isChar_of_irr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem eq_zero_of_ip {G : Type} [Group G] [Fintype G] {f : G → ℂ} (hf : IsClass f)
    (h : ∀ ρ, IsIrr ρ → ip f ρ = 0) : f = 0 := by
  calc f = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, ip f ρ • ρ := (_root_.GlobalTheory.charDec G f).2.1 hf
    _ = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, (0 : G → ℂ) :=
        finsum_mem_congr rfl fun ρ hρ => by rw [h ρ hρ, zero_smul]
    _ = 0 := finsum_mem_zero _

theorem ip_prod {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] (Φ : G₁ × G₂ → ℂ)
    (α : G₁ → ℂ) (β : G₂ → ℂ) :
    ip Φ (fun z => α z.1 * β z.2) = ip (fun y => ip (fun x => Φ (x, y)) α) β := by
  simp only [ip, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, Prod.fst_inv, Prod.snd_inv,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

theorem isIrr_prod {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    {α : G₁ → ℂ} {β : G₂ → ℂ} (hα : IsIrr α) (hβ : IsIrr β) :
    IsIrr (fun z : G₁ × G₂ => α z.1 * β z.2) := by
  have hA : IsChar (fun z : G₁ × G₂ => α z.1) :=
    (_root_.GlobalTheory.GLm.isChar_comp_hom_and_mul).1 (G₁ × G₂) G₁ (MonoidHom.fst G₁ G₂) α (isChar_of_irr hα)
  have hB : IsChar (fun z : G₁ × G₂ => β z.2) :=
    (_root_.GlobalTheory.GLm.isChar_comp_hom_and_mul).1 (G₁ × G₂) G₂ (MonoidHom.snd G₁ G₂) β (isChar_of_irr hβ)
  have hC : IsChar (fun z : G₁ × G₂ => α z.1 * β z.2) := (_root_.GlobalTheory.GLm.isChar_comp_hom_and_mul).2 (G₁ × G₂) _ _ hA hB
  apply (_root_.GlobalTheory.charDec (G₁ × G₂) _).2.2.2.1 hC
  have h1 : ip α α = 1 := by simpa using (_root_.GlobalTheory.GLq.ZOrth.zorth G₁ α α hα hα).2.2
  have h2 : ip β β = 1 := by simpa using (_root_.GlobalTheory.GLq.ZOrth.zorth G₂ β β hβ hβ).2.2
  have key : ∀ y, ip (fun x => α x * β y) α = β y := by
    intro y
    have e : ip (fun x => α x * β y) α = β y * ip α α := by
      simp only [ip, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e, h1, mul_one]
  rw [ip_prod]
  simp only [key]
  exact h2

theorem exists_prod_of_isIrr {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    {ρ : G₁ × G₂ → ℂ} (hρ : IsIrr ρ) :
    ∃ p : (G₁ → ℂ) × (G₂ → ℂ), (IsIrr p.1 ∧ IsIrr p.2) ∧ ρ = fun z => p.1 z.1 * p.2 z.2 := by
  by_contra hne
  push Not at hne
  have hcl : IsClass ρ := (_root_.GlobalTheory.charDec _ ρ).2.2.1 (isChar_of_irr hρ)
  have hip : ∀ α β, IsIrr α → IsIrr β → ip ρ (fun z : G₁ × G₂ => α z.1 * β z.2) = 0 := by
    intro α β hα hβ
    rw [(_root_.GlobalTheory.GLq.ZOrth.zorth _ ρ _ hρ (isIrr_prod hα hβ)).2.2,
      ite_eq_right (by simpa using hne (α, β) ⟨hα, hβ⟩)]
  have hrow : ∀ y, (fun x => ρ (x, y)) = 0 := by
    intro y
    apply eq_zero_of_ip
    · intro x k
      simpa using hcl (x, y) (k, 1)
    · intro α hα
      have hF : (fun y' => ip (fun x => ρ (x, y')) α) = 0 := by
        apply eq_zero_of_ip
        · intro y' h
          have e : (fun x => ρ (x, h * y' * h⁻¹)) = fun x => ρ (x, y') := by
            funext x
            simpa using hcl (x, y') (1, h)
          exact congrArg (fun f => ip f α) e
        · intro β hβ
          exact (ip_prod ρ α β).symm.trans (hip α β hα hβ)
      exact congrFun hF y
  have hz : ρ = 0 := by
    funext z
    obtain ⟨x, y⟩ := z
    exact congrFun (hrow y) x
  have h1 := (_root_.GlobalTheory.GLq.ZOrth.zorth _ ρ ρ hρ hρ).2.2
  rw [ite_eq_left rfl, hz] at h1
  simp [ip] at h1

private theorem sum_irr_prod_eq_sum_irr_mul {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    (L : List (G₁ × G₂ → ℂ)) (hL : ∀ ρ ∈ L, IsIrr ρ) :
    ∃ L' : List ((G₁ → ℂ) × (G₂ → ℂ)), (∀ p ∈ L', IsIrr p.1 ∧ IsIrr p.2) ∧
      ∀ x y, L.sum (x, y) = (L'.map fun p => p.1 x * p.2 y).sum := by
  induction L with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons ρ L ih =>
    obtain ⟨p, hp, rfl⟩ := exists_prod_of_isIrr (hL ρ (by simp))
    obtain ⟨L', hL', hsum⟩ := ih fun r hr => hL r (List.mem_cons_of_mem _ hr)
    refine ⟨p :: L', ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hp
      · exact hL' q hq
    · intro x y
      rw [List.sum_cons, Pi.add_apply, hsum]
      simp

theorem exists_list_prod : ∀ (G₁ G₂ : Type) [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] (Φ : G₁ × G₂ → ℂ),
    IsChar Φ → ∃ L : List ((G₁ → ℂ) × (G₂ → ℂ)), (∀ p ∈ L, IsIrr p.1 ∧ IsIrr p.2) ∧
      ∀ x y, Φ (x, y) = (L.map fun p => p.1 x * p.2 y).sum := by
  intro G₁ G₂ _ _ _ _ Φ hΦ
  obtain ⟨L, hL, rfl⟩ := (_root_.GlobalTheory.charDec (G₁ × G₂) Φ).1 hΦ
  exact sum_irr_prod_eq_sum_irr_mul L hL

end GlobalTheory.GLm.ProdChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentBlockUpperUnitriangular
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.DepOne

theorem Hpk_mulVec_e {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (esI k r a)]
  · have := a.isLt
    have h1 : (eI k r a).val = a.val := rfl
    have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
    unfold Hpk
    rw [if_pos (by omega), one_mul]
  · intro l _ hl
    have hl' : l.val ≠ 2 * r + k - a.val := fun h => hl (Fin.ext h)
    have := a.isLt
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · simp

theorem Hpk_e_es {k r : ℕ} (a b : Fin r) :
    Hpk k r (eI k r a) (esI k r b) = if a = b then 1 else 0 := by
  have ha := a.isLt
  have hb := b.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r b).val = 2 * r + k - b.val := rfl
  unfold Hpk
  by_cases hab : a = b
  · subst hab
    rw [if_pos (by omega), if_pos rfl]
  · have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg hab]

theorem es_es {k r : ℕ} {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hx : x ∈ Nset k r)
    (b : Fin r) : ∀ (n : ℕ) (a : Fin r), a.val = n → a ≤ b →
      x (esI k r a) (esI k r b) = if a = b then 1 else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a han hab
  have hU : xᴴ * Hpk k r * x = Hpk k r := hx.1
  have h := congrFun (congrFun hU (eI k r a)) (esI k r b)
  rw [Matrix.mul_assoc, Hpk_e_es] at h
  have hs : (xᴴ * (Hpk k r * x)) (eI k r a) (esI k r b) =
      ∑ i, star (x i (eI k r a)) * (Hpk k r *ᵥ fun l => x l (esI k r b)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [hs, Finset.sum_eq_single (eI k r a)] at h
  · rw [Hpk_mulVec_e, hx.2.1 a (eI k r a) le_rfl, if_pos rfl, star_one, one_mul] at h
    exact h
  · intro i _ hi
    by_cases hia : a.val ≤ i.val
    · rw [hx.2.1 a i hia, if_neg hi, star_zero, zero_mul]
    · have ha := a.isLt
      obtain ⟨c, rfl⟩ : ∃ c : Fin r, i = eI k r c := ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
      have hca : c.val < a.val := by simpa [eI] using not_le.1 hia
      rw [Hpk_mulVec_e]
      have hcb : c ≤ b := le_trans (le_of_lt (show c < a from hca)) hab
      rw [ih c.val (han ▸ hca) c rfl hcb, if_neg (fun h => by
        subst h; exact absurd hab (not_le.2 hca)), mul_zero]
  · simp

theorem dep_one : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    x ∈ Nset k r → Dep k r 1 (x - 1) := by
  intro k r x hx i j hij
  rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
  have hi := i.isLt
  have hj := j.isLt
  simp only [pos] at hij
  by_cases hjr : j.val < r
  · have hji : j.val ≤ i.val := by split_ifs at hij <;> omega
    have e : j = eI k r ⟨j.val, hjr⟩ := Fin.ext rfl
    have := hx.2.1 ⟨j.val, hjr⟩ i hji
    rw [← e] at this
    exact this
  by_cases hjm : j.val ≤ r + k
  · have hri : r ≤ i.val := by split_ifs at hij <;> omega
    exact hx.2.2 i j (by omega) hjm hri
  · have hji : j.val ≤ i.val := by split_ifs at hij <;> omega
    have hb : 2 * r + k - j.val < r := by omega
    have hc : 2 * r + k - i.val < r := by omega
    have ej : j = esI k r ⟨2 * r + k - j.val, hb⟩ := Fin.ext (by simp [esI]; omega)
    have ei : i = esI k r ⟨2 * r + k - i.val, hc⟩ := Fin.ext (by simp [esI]; omega)
    have key := es_es hx ⟨2 * r + k - j.val, hb⟩ _ ⟨2 * r + k - i.val, hc⟩ rfl
      (by rw [Fin.mk_le_mk]; omega)
    rw [← ei, ← ej] at key
    rw [key]
    by_cases hij' : i = j
    · subst hij'; simp
    · rw [if_neg hij', if_neg]
      intro h
      apply hij'
      rw [ei, ej, h]

end GlobalTheory.SnMass.VolN.DepOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericLocalTermsSelfDualLatticesStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_local_terms_selfDual_lattices : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ Λ : Submodule M.L.O V, ((H.IsSelfDual Λ ∧ Λ.FG ∧ (∀ i, H.MMfam (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) i ∈ Λ) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ↔ ∃ d : LocNG.Datum P, LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ∧ ∀ d d' : LocNG.Datum P, LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) → LocNG.IsTermOver P d' (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) → d = d' := by
  first | exact @GlobalTheory.HL.GenericTerm.generic_terms | exact GlobalTheory.HL.GenericTerm.generic_terms | (intros; apply GlobalTheory.HL.GenericTerm.generic_terms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
section
open NumberField

noncomputable section
namespace GlobalTheory.SnMass.SkewVol

variable {E : Type} [Field E] [NumberField E]

def reV (x : E) : InfinitePlace E → ℝ := fun w => (w.embedding x).re

def imV (x : E) : InfinitePlace E → ℝ := fun w => (w.embedding x).im

end GlobalTheory.SnMass.SkewVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHsNormSqMatrixCoeffLeFormalDegree
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.EllBound

theorem exists_inner_eq_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {v : E}
    (hv : v ≠ 0) : ∃ ξ : E, ⟪v, ξ⟫_ℂ = 1 ∧ ⟪ξ, v⟫_ℂ = 1 := by
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv
  refine ⟨(⟪v, v⟫_ℂ)⁻¹ • v, ?_, ?_⟩
  · rw [inner_smul_right]
    exact inv_mul_cancel₀ hvv
  · rw [inner_smul_left, map_inv₀, inner_conj_symm]
    exact inv_mul_cancel₀ hvv

theorem lintegral_hsNormSq_ell_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ (l : H → Wp) (l' : H → Wq), IsEll z (psiGen k r z c) π μS σ (DD σ w) l → IsEll z' (psiGen k r z' c') π' μS' σ (DD σ w) l' → ∫⁻ γ, ENNReal.ofReal (hsNormSq ((d : ℂ) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal d⁻¹ := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hS hS' ν hν l l' hl hl'

  obtain ⟨w₀, hw₀, hlw₀⟩ := hl.2.1
  obtain ⟨w₀', hw₀', hlw₀'⟩ := hl'.2.1
  obtain ⟨ξ, hξ₁, hξ₂⟩ := exists_inner_eq_one hlw₀
  obtain ⟨ξ', hξ₁', hξ₂'⟩ := exists_inner_eq_one hlw₀'

  have hbe : (⟪ξ, be (psiGen k r z c) π μS σ w₀ w₀ ξ⟫_ℂ).re = 1 := by
    rw [hl.2.2 w₀ hw₀ w₀ hw₀, rankOneInnerOperator_apply, inner_smul_right, hξ₁, hξ₂]
    simp
  have hbe' : (⟪ξ', be (psiGen k r z' c') π' μS' σ w₀' w₀' ξ'⟫_ℂ).re = 1 := by
    rw [hl'.2.2 w₀' hw₀' w₀' hw₀', rankOneInnerOperator_apply, inner_smul_right, hξ₁', hξ₂']
    simp
  have hbound := _root_.GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' ν hν
    w₀' hw₀' w₀ hw₀ ξ ξ'
  rw [hbe, hbe', mul_one, mul_one] at hbound
  refine le_trans (le_of_eq ?_) hbound

  have hreg : ∀ᵐ γ ∂ν, Matrix.of γ ∈ Greg k r z z' := ae_iff.mpr hν.2.1
  refine lintegral_congr_ae ?_
  filter_upwards [hreg] with γ hγ
  rw [(_root_.GlobalTheory.SgInf.EllName.iint_eq_ell k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' l l' hl hl' _ hγ).2
    w₀ hw₀ w₀' hw₀' ξ ξ', hξ₁, hξ₂']
  simp

end GlobalTheory.SgInf.EllBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralPiProdMulFintypeProduct
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem lintegral_pi_prod_mul : ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν] (f : ∀ i, X i → ENNReal) (g : Y → ENNReal), (∀ i, Measurable (f i)) → Measurable g → ∫⁻ p, (∏ i, f i (p.1 i)) * g p.2 ∂((Measure.pi μ).prod ν) = (∏ i, ∫⁻ y, f i y ∂(μ i)) * ∫⁻ y, g y ∂ν := by
  intro ι _ X _ μ _ Y _ ν _ f g hf hg
  have hm : Measurable fun x : ∀ i, X i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)
  rw [← GlobalTheory.SnMass.Push.lintegral_fintype_prod f hf]
  exact lintegral_prod_mul hm.aemeasurable hg.aemeasurable

end GlobalTheory.StabUnfold
end

