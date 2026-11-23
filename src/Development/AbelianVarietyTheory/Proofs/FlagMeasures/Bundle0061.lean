module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0055
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabilizerInfLeConjNormalisingSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Formalism.LocalRingCardinality.DataSpaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0056

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductParamsIntegral
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.SAN.IntParam

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem eich_int (L : LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) {x u v : Fin N → E} {s : E} (hx : ∀ j, x j ∈ L.O)
    (hu : ∀ j, u j ∈ L.O) (hs : s ∈ L.O) (hv : ∀ j, v j ∈ L.O) (j : Fin N) :
    eich L Hm x u s v j ∈ L.O := by
  simp only [eich, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact L.O.sub_mem (L.O.add_mem (hv j) (L.O.mul_mem (hf_int L hI hv hu) (hx j)))
    (L.O.mul_mem (hf_int L hI hv hx) (L.O.add_mem (hu j) (L.O.mul_mem hs (hx j))))

theorem prod_fix {N : ℕ} (y : Fin N → E) :
    ∀ l : List ((Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ g ∈ l, g y = y) → l.prod y = y := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons g l ih =>
    intro h
    rw [List.prod_cons, LinearEquiv.mul_apply, ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')),
      h g List.mem_cons_self]

theorem finiteRing_sq_sub_mul_sq_eq_of_card (L : LocE F E) (N : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : IsHerm L Hm)
    (hI : ∀ i j, Hm i j ∈ L.O) : ∀ (r : ℕ) (X Y u : Fin r → Fin N → E) (s : Fin r → E)
    (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i j, X i j ∈ L.O) → (∀ i j, Y i j ∈ L.O) →
    (∀ a b, hf L Hm (X a) (Y b) = if a = b then 1 else 0) → (∀ a b, hf L Hm (X a) (X b) = 0) →
    (∀ i, ∀ j, j ≤ i → hf L Hm (u i) (X j) = 0 ∧ hf L Hm (u i) (Y j) = 0) →
    (∀ i, s i + L.cj (s i) = hf L Hm (u i) (u i)) →
    (∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) →
    (∀ x : Fin N → E, (∀ j, (List.ofFn e).prod x j ∈ L.O) ↔ ∀ j, x j ∈ L.O) →
    (∀ i j, u i j ∈ L.O) ∧ ∀ i, s i ∈ L.O := by
  intro r
  induction r with
  | zero => intro X Y u s e _ _ _ _ _ _ _ _; exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ r ih =>
    intro X Y u s e hX hY hXY hXX hu hs he hn
    set n' := (List.ofFn fun i : Fin r => e i.succ).prod with hn'def
    have hprod : ∀ x, (List.ofFn e).prod x = e 0 (n' x) := by
      intro x; rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply]

    have hfix : n' (Y 0) = Y 0 := by
      refine prod_fix (Y 0) _ fun g hg => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
      have h1 : hf L Hm (Y 0) (u i.succ) = 0 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, (hu i.succ 0 (Fin.zero_le _)).2, map_zero]
      have h2 : hf L Hm (Y 0) (X i.succ) = 0 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, hXY, if_neg (Fin.succ_ne_zero i), map_zero]
      rw [he, eich, h1, h2]; simp
    have h0 : e 0 (Y 0) = Y 0 - (u 0 + s 0 • X 0) := by
      have h1 : hf L Hm (Y 0) (u 0) = 0 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, (hu 0 0 le_rfl).2, map_zero]
      have h2 : hf L Hm (Y 0) (X 0) = 1 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, hXY, if_pos rfl, map_one]
      rw [he, eich, h1, h2]; simp
    have hnY : ∀ j, (List.ofFn e).prod (Y 0) j ∈ L.O := (hn (Y 0)).2 (hY 0)
    rw [hprod, hfix, h0] at hnY
    have hw : ∀ j, (u 0 + s 0 • X 0) j ∈ L.O := by
      intro j
      have := L.O.sub_mem (hY 0 j) (hnY j)
      simpa using this
    have hs0 : s 0 ∈ L.O := by
      have h := hf_int L hI hw (hY 0)
      rwa [GlobalTheory.HL.Eichler.hf_add_l, GlobalTheory.HL.Eichler.hf_smul_l, (hu 0 0 le_rfl).2, hXY, if_pos rfl,
        mul_one, zero_add] at h
    have hu0 : ∀ j, u 0 j ∈ L.O := by
      intro j
      have h := L.O.sub_mem (hw j) (L.O.mul_mem hs0 (hX 0 j))
      simpa using h

    have he0 : ∀ x, (∀ j, e 0 x j ∈ L.O) ↔ ∀ j, x j ∈ L.O := by
      intro x
      constructor
      · intro h j
        have hinv := GlobalTheory.HL.Eichler.eich_inv L hH (X 0) (u 0) (s 0) (hXX 0 0) (hu 0 0 le_rfl).1 (hs 0) x
        rw [← hinv, ← he]
        exact eich_int L hI (hX 0) (fun k => L.O.neg_mem (hu0 k)) (GlobalTheory.UnramOrder.cj_mem L hs0) h j
      · intro h j
        rw [he]
        exact eich_int L hI (hX 0) hu0 hs0 h j
    have hn2 : ∀ x : Fin N → E, (∀ j, (List.ofFn fun i : Fin r => e i.succ).prod x j ∈ L.O) ↔
        ∀ j, x j ∈ L.O := by
      intro x
      rw [← hn x, hprod, ← hn'def]
      exact (he0 (n' x)).symm
    obtain ⟨hU, hS⟩ := ih (fun i => X i.succ) (fun i => Y i.succ) (fun i => u i.succ)
      (fun i => s i.succ) (fun i => e i.succ) (fun i => hX i.succ) (fun i => hY i.succ)
      (fun a b => by rw [hXY]; simp only [Fin.succ_inj]) (fun a b => hXX a.succ b.succ)
      (fun i j hj => hu i.succ j.succ (Fin.succ_le_succ_iff.mpr hj)) (fun i => hs i.succ)
      (fun i v => he i.succ v) hn2
    refine ⟨fun i => Fin.cases hu0 (fun i => hU i) i, fun i => Fin.cases hs0 (fun i => hS i) i⟩

theorem eich_prod_params_int : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : IsHerm L Hm) (hI : ∀ i j, Hm i j ∈ L.O) (X Y u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (hX : ∀ i j, X i j ∈ L.O) (hY : ∀ i j, Y i j ∈ L.O) (hXY : ∀ a b, hf L Hm (X a) (Y b) = if a = b then 1 else 0) (hXX : ∀ a b, hf L Hm (X a) (X b) = 0) (hu : ∀ i, ∀ j, j ≤ i → hf L Hm (u i) (X j) = 0 ∧ hf L Hm (u i) (Y j) = 0) (hs : ∀ i, s i + L.cj (s i) = hf L Hm (u i) (u i)) (he : ∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) (hn : ∀ x : Fin N → E, (∀ j, (List.ofFn e).prod x j ∈ L.O) ↔ ∀ j, x j ∈ L.O), (∀ i j, u i j ∈ L.O) ∧ ∀ i, s i ∈ L.O := by
  intro F _ _ _ _ _ E _ _ _ L N r Hm hH hI X Y u s e hX hY hXY hXX hu hs he hn
  exact finiteRing_sq_sub_mul_sq_eq_of_card L N Hm hH hI r X Y u s e hX hY hXY hXX hu hs he hn

end GlobalTheory.HL.SAN.IntParam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFlagDualBasis
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.UnitriangularCoeff

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem sigR_inclR (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

def hRight (x : Fin n → R ⊗[F] E) : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun y := hR R σ J x y
  map_add' y z := by
    simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hRight_apply (x y : Fin n → R ⊗[F] E) : hRight R σ J x y = hR R σ J x y := rfl

theorem hR_add_right (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y + z) = hR R σ J x y + hR R σ J x z := (hRight R σ J x).map_add y z

theorem hR_sub_right (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y - z) = hR R σ J x y - hR R σ J x z := (hRight R σ J x).map_sub y z

theorem hR_smul_right (x y : Fin n → R ⊗[F] E) (c : R ⊗[F] E) :
    hR R σ J x (c • y) = c * hR R σ J x y := (hRight R σ J x).map_smul c y

theorem hR_zero_right (x : Fin n → R ⊗[F] E) : hR R σ J x 0 = 0 := (hRight R σ J x).map_zero

theorem hR_ratV (x y : Fin n → E) :
    hR R σ J (ratV (F := F) R x) (ratV (F := F) R y) = inclR R (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hE, Formalism.UG.hform, ratV, JR, Matrix.map_apply, map_sum, map_mul, sigR_inclR,
    AlgHom.coe_toRingHom, RingHom.coe_coe]

theorem hE_symm (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (x y : Fin n → E) :
    hE σ J y x = σ (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ.1 b a]
  ring

variable {R σ J}

theorem hermitian_flag_dual_basis (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (a : Fin r) (c : Fin (r + 1)) :
    hE σ J (P.f a) (F0 P c) = if c = a.castSucc then 1 else 0 := by
  induction c using Fin.lastCases with
  | last =>
    rw [F0, Fin.snoc_last, hP.2.2.2.2.1 a, if_neg (Fin.castSucc_lt_last a).ne']
  | cast c =>
    rw [F0, Fin.snoc_castSucc, hE_symm σ J hσ hJ, hP.2.2.1 c a]
    by_cases h : c = a
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e)), map_zero]

theorem pairR (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (a : Fin r) (c : Fin (r + 1)) :
    hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R (F0 P c)) = if c = a.castSucc then 1 else 0 := by
  rw [hR_ratV, hermitian_flag_dual_basis hσ hJ hP a c]
  split_ifs <;> simp only [map_one, map_zero]

theorem pair_sum (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (a : Fin r) (c : Fin (r + 1) → R ⊗[F] E) :
    hR R σ J (ratV (F := F) R (P.f a)) (∑ b, c b • ratV (F := F) R (F0 P b)) = c a.castSucc := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hRight_apply, map_sum]
  simp only [map_smul, hRight_apply, pairR hσ hJ hP, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem expand (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (b : Fin (r + 1)) (w : Fin n → R ⊗[F] E)
    (hw : w ∈ spanR (F := F) R (F0 P) {a | a < b}) :
    w = ∑ a, (if h : a < b then hR R σ J (ratV (F := F) R
      (P.f (a.castLT (lt_of_lt_of_le h (Fin.le_last b))))) w else 0) • ratV (F := F) R (F0 P a) := by
  unfold spanR at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    have hc' : c < b := hc
    symm
    rw [Finset.sum_eq_single c]
    · rw [dite_eq_left hc', pairR hσ hJ hP, Fin.castSucc_castLT, if_pos rfl, one_smul]
    · intro a _ hac
      split_ifs with h
      · rw [pairR hσ hJ hP, Fin.castSucc_castLT, if_neg (fun e => hac e.symm), zero_smul]
      · rw [zero_smul]
    · intro h; exact absurd (Finset.mem_univ c) h
  | zero =>
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs <;> simp [hR_zero_right]
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [hR_add_right, add_smul]
  | smul c x _ hx =>
    conv_lhs => rw [hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [hR_smul_right, smul_smul]

end Alg

theorem combine {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {r : ℕ} (b : Fin (r + 1))
    (G : Fin (r + 1) → M) (y : ∀ a : Fin (r + 1), a < b → A) :
    (∑ a, (if h : a < b then y a h else 0) • G a) + G b =
      ∑ a, (if a = b then 1 else if h : a < b then y a h else 0) • G a := by
  have key : ∀ a, (if a = b then (1 : A) else if h : a < b then y a h else 0) • G a =
      (if h : a < b then y a h else 0) • G a + (if a = b then G a else 0) := by
    intro a
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [hσ.2.2.2 τ, hσ.2.2.2 τ, star_star]

theorem exists_coeff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ ν : Ssub (Fv F v) σ J P → ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), Continuous ν ∧ ∀ (s : Ssub (Fv F v) σ J P) (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), x = ν s ↔ ∀ b, lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a) := by
  intro F E _ _ _ _ _ σ hσ n J hJ v r P T hP
  have hss : ∀ x, σ (σ x) = x := sigma_sigma σ hσ
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have ha : ∀ p : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}, (p.1.1 : ℕ) < r :=
    fun p => lt_of_lt_of_le p.2 (Fin.le_last _)
  refine ⟨fun s p => hR (Fv F v) σ J (ratV (F := F) (Fv F v) (P.f (p.1.1.castLT (ha p))))
      (lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P p.1.2))), ?_, ?_⟩
  · refine continuous_pi fun p => ?_
    have hM : Continuous fun s : Ssub (Fv F v) σ J P =>
        ((HA.mat (Fv F v) σ J (s : HA (Fv F v) σ J) : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hMij : ∀ i j, Continuous fun s : Ssub (Fv F v) σ J P =>
        ((HA.mat (Fv F v) σ J (s : HA (Fv F v) σ J) : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j :=
      fun i j => (continuous_apply j).comp ((continuous_apply i).comp hM)
    simp only [hR, Formalism.UG.hform, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_finsetSum _ fun k _ => (hMij j k).mul continuous_const)
  · intro s x
    constructor
    · rintro rfl b
      have hU : lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P b)) -
          ratV (F := F) (Fv F v) (F0 P b) ∈ spanR (F := F) (Fv F v) (F0 P) {a | a < b} := s.2 b
      have e1 := sub_eq_iff_eq_add.mp (expand hss hJ hP b _ hU)
      refine e1.trans ((combine b _ _).trans ?_)
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      split_ifs with h1 h2
      · rfl
      · rw [hR_sub_right, pairR hss hJ hP, Fin.castSucc_castLT, if_neg h2.ne', sub_zero]
      · rfl
    · intro H
      funext p
      obtain ⟨⟨a, b⟩, h⟩ := p
      symm
      show hR (Fv F v) σ J (ratV (F := F) (Fv F v) (P.f (a.castLT (lt_of_lt_of_le h (Fin.le_last b)))))
        (lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P b))) = x ⟨(a, b), h⟩
      rw [H b, pair_sum hss hJ hP, Fin.castSucc_castLT, if_neg h.ne, dite_eq_left h]

end GlobalTheory.UnitriangularCoeff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabilizerInfLeConjNormalisingSubgroupStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∃ h ∈ S.St, S.St ⊓ stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ≤ MulAut.conj h • S.K0 ∧ ∃ u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u ∧ (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧ ∀ j, h⁻¹ (n (S.f j)) = ∑ i, u i j • S.f i := by
  first | exact @GlobalTheory.HL.StabConj.main | exact GlobalTheory.HL.StabConj.main | (intros; apply GlobalTheory.HL.StabConj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeMapComapOfLeConjMaximalCmData
section
open NumberField IsDedekindDomain

namespace GlobalTheory.UnramifiedConj

theorem exists_of_fixed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (y : 𝓞 E)
    (hy : RingOfIntegers.mapRingHom (starRingEnd E) y = y) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a = y := by
  have hfix : star (y : E) = (y : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) hy
    simpa only [RingOfIntegers.mapRingHom_apply, starRingEnd_apply] using h
  obtain ⟨b, hb⟩ := (hc.fixed (y : E)).1 hfix

  have hint : IsIntegral ℤ b := by
    have hy' : IsIntegral ℤ (algebraMap F E b) := by
      rw [hb]
      exact RingOfIntegers.isIntegral_coe y
    exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).mp hy'
  refine ⟨⟨b, hint⟩, ?_⟩
  ext
  exact hb

private lemma mem_map_comap_of_star_fixed {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (Q : Ideal (𝓞 E))
    (z : 𝓞 E) (hz : RingOfIntegers.mapRingHom (starRingEnd E) z = z) (hzQ : z ∈ Q) :
    z ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
  obtain ⟨a, ha⟩ := exists_of_fixed hc z hz
  rw [← ha]
  apply Ideal.mem_map_of_mem
  rw [Ideal.mem_comap, ha]
  exact hzQ

theorem le_map_comap_of_le_conj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (P Q : Ideal (𝓞 E)) (hQ : Q.IsMaximal)
    (h1 : P ≤ Q) (h2 : P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E))) :
    P ≤ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
  have hinv : ∀ z : 𝓞 E, RingOfIntegers.mapRingHom (starRingEnd E)
      (RingOfIntegers.mapRingHom (starRingEnd E) z) = z := by
    intro z
    ext
    simp only [RingOfIntegers.mapRingHom_apply, starRingEnd_apply, star_star]

  have hD : Ideal.span (Set.range fun θ : 𝓞 E => θ - RingOfIntegers.mapRingHom (starRingEnd E) θ)
      = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hDM⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨_, _, hU⟩ := hc.cmUnram
    obtain ⟨θ, t, ht, hθ⟩ := hU M hM
    have htθ : t = RingOfIntegers.mapRingHom (starRingEnd E) θ := by
      ext
      rw [RingOfIntegers.mapRingHom_apply, starRingEnd_apply]
      exact ht
    subst htθ
    exact hθ (hDM (Ideal.subset_span ⟨θ, rfl⟩))
  intro x hx
  have hxQ : x ∈ Q := h1 hx
  have hsxQ : RingOfIntegers.mapRingHom (starRingEnd E) x ∈ Q := h2 hx

  have hgen : ∀ θ : 𝓞 E,
      x * (θ - RingOfIntegers.mapRingHom (starRingEnd E) θ) ∈
        Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
    intro θ
    set s := RingOfIntegers.mapRingHom (starRingEnd E) with hs
    have e : x * (θ - s θ) = (x + s x) * θ - (x * s θ + s x * θ) := by ring
    rw [e]
    refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ ?_) ?_
    · refine mem_map_comap_of_star_fixed hc Q _ ?_ (Q.add_mem hxQ hsxQ)
      rw [map_add (f := _), hinv]
      ring
    · refine mem_map_comap_of_star_fixed hc Q _ ?_
        (Q.add_mem (Q.mul_mem_right _ hxQ) (Q.mul_mem_right _ hsxQ))
      rw [map_add (f := _), map_mul, map_mul, hinv, hinv]
      ring
  have key : ∀ d ∈ Ideal.span (Set.range fun θ : 𝓞 E =>
      θ - RingOfIntegers.mapRingHom (starRingEnd E) θ),
      x * d ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨θ, rfl⟩ := hd
      exact hgen θ
    | zero => simp
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ c ha
  have h1 : (1 : 𝓞 E) ∈ Ideal.span (Set.range fun θ : 𝓞 E =>
      θ - RingOfIntegers.mapRingHom (starRingEnd E) θ) := by
    rw [hD]
    exact Submodule.mem_top
  simpa using key 1 h1

end GlobalTheory.UnramifiedConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLatticeBetweenScaledStandardLatticesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_between_scaled_standard_lattices : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (p : HeightOneSpectrum (𝓞 F)) (n : ℕ) (Λ : Submodule (A.L p).O (Fin n → (A.loc p).Ep)), IsLat (A.L p) Λ → (∀ y : (A.loc p).Ep, ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O) → ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) → (m : (A.loc p).Ep) • v ∈ Λ) ∧ ∀ v ∈ Λ, ∀ i, (m : (A.loc p).Ep) * v i ∈ (A.L p).O := by
  first | exact @GlobalTheory.HL.Glue.lat_between | exact GlobalTheory.HL.Glue.lat_between | (intros; apply GlobalTheory.HL.Glue.lat_between <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLatticeLeCompletionGluedLatticeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLattice_le_completion_glued_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep)) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), (∀ x, x ∈ Γ ↔ ∀ p, A.bc p x ∈ Λ p) → (∀ p (v : Fin n → (A.loc p).Ep), (∀ i, v i ∈ (A.L p).O) → (N : (A.loc p).Ep) • v ∈ Λ p) → (∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite → ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = (N : (A.loc p).Ep) * o) → ∀ p, Λ p ≤ A.lat p Γ := by
  first | exact @GlobalTheory.HL.Glue.local_le_lat_of_approx | exact GlobalTheory.HL.Glue.local_le_lat_of_approx | (intros; apply GlobalTheory.HL.Glue.local_le_lat_of_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NatCastIsUnitQuadraticCompletionAlmostAllStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCast_isUnit_quadraticCompletion_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (N : ℕ), N ≠ 0 → {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (N : (A.loc p).Fp)}.Finite := by
  first | exact @GlobalTheory.HL.Glue.natCast_isUnit_ae | exact GlobalTheory.HL.Glue.natCast_isUnit_ae | (intros; apply GlobalTheory.HL.Glue.natCast_isUnit_ae <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqInvStabilizerVolumeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_mass_eq_inv_stabilizer_volume : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), ∃ V0 : ℝ≥0∞, ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = V0 * ENNReal.ofReal (invVol K0 (MulAction.stabilizer G x)) := by
  first | exact @GlobalTheory.HL.mass_orbit_eq | exact GlobalTheory.HL.mass_orbit_eq | (intros; apply GlobalTheory.HL.mass_orbit_eq <;> assumption)
end

