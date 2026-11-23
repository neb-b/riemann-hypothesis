module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormGaussSumLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate

namespace GlobalTheory.HL.GaussSummand

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_add_left (x y z : Fin n → E) : hf L Hm (x + y) z = hf L Hm x z + hf L Hm y z := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y z : Fin n → E) : hf L Hm x (y + z) = hf L Hm x y + hf L Hm x z := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_left (c : E) (x z : Fin n → E) : hf L Hm (c • x) z = c * hf L Hm x z := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_smul_right (c : E) (x z : Fin n → E) : hf L Hm x (c • z) = L.cj c * hf L Hm x z := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hf_zero_left (z : Fin n → E) : hf L Hm 0 z = 0 := by
  simp [hf]

theorem hf_sum_left {ι : Type*} (s : Finset ι) (x : ι → Fin n → E) (z : Fin n → E) :
    hf L Hm (∑ a ∈ s, x a) z = ∑ a ∈ s, hf L Hm (x a) z := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_left, ih]

theorem cj_hf (h : IsHerm L Hm) (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by
  have h' : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun h i) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end

theorem norm_gauss_sum_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ψ : AddChar F ℂ), (∀ x : F, ‖ψ x‖ = 1) → (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) → ∀ (UU : Submodule L.O (Fin n → E)), (∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O) → ∀ (ρ : ℕ) (e : Fin ρ → Fin n → E), (∀ a, e a ∈ UU) → (∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) → ∀ (i N : ℕ), 1 ≤ i → i ≤ N → ∀ (t : F) (u₀ : (𝒪[F])ˣ), t * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) → ∀ (χ : AddChar (Fin n → E) ℂ), (∀ u, ‖χ u‖ = 1) → (∀ u ∈ UU, χ (algebraMap F E ((ϖ : F) ^ N) • u) = 1) → ∀ (R : Finset (Fin n → E)) (nrm : (Fin n → E) → F), (∀ u, algebraMap F E (nrm u) = hf L Hm u u) → (∀ u ∈ R, u ∈ UU) → (∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y) → ‖∑ u ∈ R, ψ (t * nrm u) * χ u‖ ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(i * ρ : ℤ)) := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH ϖ hϖ ψ hψ1 hψ UU hUU d e heU hee i N _ hiN t u₀ ht χ hχ1 hχ
    R nrm hnrm hRO hR
  obtain ⟨-, -, hdual, -, hint, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hO : ∀ c : 𝒪[F], algebraMap F E c ∈ L.O := fun c => (hint c).2 c.2
  have hsm : ∀ c ∈ L.O, ∀ x ∈ UU, c • x ∈ UU := fun c hc x hx =>
    UU.smul_mem (⟨c, hc⟩ : L.O) hx
  let I : ℕ → Ideal L.O := fun j => Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)}
  have hI : ∀ j (x : L.O), x ∈ I j ↔ ∃ c ∈ L.O, (x : E) = algebraMap F E ((ϖ : F) ^ j) * c := by
    intro j x
    have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)}
        = {⟨algebraMap F E ((ϖ : F) ^ j), hO (ϖ ^ j)⟩} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff]
    simp only [I]
    rw [hset, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, c.2, congrArg Subtype.val hc⟩
    · rintro ⟨c, hc, h⟩
      exact ⟨⟨c, hc⟩, Subtype.ext h⟩
  let P₀ : AddSubgroup (Fin d → L.O) := AddSubgroup.pi Set.univ fun _ => (I i).toAddSubgroup
  have hP₀ : ∀ x, x ∈ P₀ ↔ ∀ a, ∃ c ∈ L.O, (x a : E) = algebraMap F E ((ϖ : F) ^ i) * c := by
    intro x
    simp only [P₀, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup, hI]
  have hidx₀ : P₀.index = (resQ ϖ ^ (i * d)) ^ 2 := by
    have : (I i).toAddSubgroup.index = resQ ϖ ^ (2 * i) := hcard i
    simp only [P₀]
    rw [AddSubgroup.index_pi, Finset.prod_const, this, Finset.card_univ, Fintype.card_fin]
    ring
  let φ : UU →+ (Fin d → L.O) :=
    { toFun := fun m a => ⟨hf L Hm m (e a), hUU _ m.2 _ (heU a)⟩
      map_zero' := funext fun a => Subtype.ext (hf_zero_left L Hm _)
      map_add' := fun x y => funext fun a => Subtype.ext (hf_add_left L Hm _ _ _) }
  have hφ : Function.Surjective φ := fun c => by
    refine ⟨⟨∑ b, (c b : E) • e b, UU.sum_mem fun b _ => hsm _ (c b).2 _ (heU b)⟩,
      funext fun a => Subtype.ext ?_⟩
    show hf L Hm (∑ b, (c b : E) • e b) (e a) = c a
    simp [hf_sum_left, hf_smul_left, hee]
  let Q : AddSubgroup UU := P₀.comap φ
  have hQ : ∀ x : UU, x ∈ Q ↔
      ∀ a, ∃ c ∈ L.O, hf L Hm x (e a) = algebraMap F E ((ϖ : F) ^ i) * c := fun x => hP₀ (φ x)
  have hidx : Q.index = (resQ ϖ ^ (i * d)) ^ 2 := by
    rw [← hidx₀]; exact AddSubgroup.index_comap_of_surjective P₀ hφ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hiN
  let P : AddSubgroup UU :=
    { carrier := {x | ∃ y ∈ UU, (x : Fin n → E) = algebraMap F E ((ϖ : F) ^ (i + k)) • y}
      zero_mem' := ⟨0, UU.zero_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨x', hx', hx⟩ ⟨y', hy', hy⟩
        exact ⟨x' + y', UU.add_mem hx' hy', by rw [Submodule.coe_add, hx, hy, smul_add]⟩
      neg_mem' := by
        rintro x ⟨x', hx', hx⟩
        exact ⟨-x', UU.neg_mem hx', by rw [Submodule.coe_neg, hx, smul_neg]⟩ }
  have hP : ∀ x : UU, x ∈ P ↔
      ∃ y ∈ UU, (x : Fin n → E) = algebraMap F E ((ϖ : F) ^ (i + k)) • y := fun _ => Iff.rfl
  have hPQ : P ≤ Q := fun x hx => (hQ x).2 fun a => by
    obtain ⟨y, hy, h⟩ := (hP x).1 hx
    refine ⟨algebraMap F E ((ϖ : F) ^ k) * hf L Hm y (e a),
      L.O.mul_mem (hO (ϖ ^ k)) (hUU _ hy _ (heU a)), ?_⟩
    rw [h, hf_smul_left, pow_add, map_mul, mul_assoc]
  have hιinj : Function.Injective (Subtype.val : UU → Fin n → E) := Subtype.val_injective
  have hrange : ∀ u ∈ R, u ∈ Set.range (Subtype.val : UU → Fin n → E) :=
    fun u hu => ⟨⟨u, hRO u hu⟩, rfl⟩
  let R' := R.preimage (Subtype.val : UU → Fin n → E) hιinj.injOn
  have hτ : algebraMap F E t * algebraMap F E ((ϖ : F) ^ i)
      = algebraMap F E ((u₀ : 𝒪[F]) : F) := by rw [← map_mul, ht]
  have key := GaussSum.sq_norm_sum_reps_mul_index_le P Q hPQ R' ?_
    (fun m => ψ (t * nrm m) * χ m) (fun m => by rw [norm_mul, hψ1, hχ1, mul_one]) ?_ ?_
  · rw [Finset.sum_preimage Subtype.val R hιinj.injOn (fun u => ψ (t * nrm u) * χ u)
      (fun u hu h => (h (hrange u hu)).elim), Finset.card_preimage, hidx,
      Finset.filter_true_of_mem hrange, Nat.cast_pow, ← mul_pow] at key
    have hq0 : (0 : ℝ) < resQ ϖ := by exact_mod_cast (by omega : 0 < resQ ϖ)
    have h := (sq_le_sq₀ (by positivity) (by positivity)).1 key
    rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact_mod_cast h
  · intro u
    obtain ⟨w, ⟨hw, hw'⟩, huniq⟩ := hR u u.2
    obtain ⟨w, rfl⟩ := hrange w hw
    refine ⟨w, ⟨Finset.mem_preimage.2 hw, (hP _).2 hw'⟩, fun y hy => hιinj ?_⟩
    exact huniq _ ⟨Finset.mem_preimage.1 hy.1, (hP _).1 hy.2⟩
  · intro u p hp
    obtain ⟨c, hc, hpc⟩ := (hP p).1 hp
    have h1 : χ p = 1 := by rw [hpc, hχ c hc]
    have h3 : t * (nrm (u + p) - nrm u) ∈ 𝒪[F] := by
      rw [← hint, map_mul, map_sub, hnrm, hnrm]
      have : algebraMap F E t * (hf L Hm (u + p) (u + p) - hf L Hm u u)
          = algebraMap F E ((u₀ : 𝒪[F]) : F) * algebraMap F E ((ϖ : F) ^ k)
            * (hf L Hm c (u + p) + hf L Hm u c) := by
        have e1 : hf L Hm p (u + p) = algebraMap F E ((ϖ : F) ^ (i + k)) * hf L Hm c (u + p) := by
          rw [← hf_smul_left, ← hpc]
        have e2 : hf L Hm u p = algebraMap F E ((ϖ : F) ^ (i + k)) * hf L Hm u c := by
          rw [hpc, hf_smul_right, AlgEquiv.commutes]
        rw [hf_add_left, e1, hf_add_right L Hm u u p, e2, ← hτ, pow_add, map_mul]
        ring
      rw [this]
      exact L.O.mul_mem (L.O.mul_mem (hO _) (hO (ϖ ^ k)))
        (L.O.add_mem (hUU _ hc _ (UU.add_mem u.2 p.2)) (hUU _ u.2 _ hc))
    have h4 := (hψ _).2 h3 1
    have h5 : t * nrm (u + p) = t * nrm u
        + t * (nrm (u + p) - nrm u) * ((1 : 𝒪[F]) : F) := by
      push_cast; ring
    show ψ (t * nrm (u + p)) * χ (u + p) = _
    rw [h5, AddChar.map_add_eq_mul, h4, mul_one, AddChar.map_add_eq_mul, h1, mul_one]
  · intro h hh
    obtain ⟨a, ha⟩ := not_forall.1 fun h' => hh ((hQ h).2 h')
    obtain ⟨z, hz⟩ : ∃ z, z = hf L Hm h (e a) := ⟨_, rfl⟩
    rw [← hz] at ha
    have h1 : algebraMap F E t * z ∉ L.O := fun h' => ha
      ⟨algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (algebraMap F E t * z),
        L.O.mul_mem (hO _) h', by
          have h2 : algebraMap F E ((u₀ : 𝒪[F]) : F)
              * algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) = 1 := by
            rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
          linear_combination (-z) * h2
            - algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * z * hτ⟩
    obtain ⟨b, hb⟩ := not_forall.1 fun h' => h1 (hdual _ h')
    obtain ⟨hb, hb'⟩ := Classical.not_imp.1 hb
    obtain ⟨s, hs⟩ := (L.cj_fix (algebraMap F E t * z * L.cj b
      + L.cj (algebraMap F E t * z * L.cj b))).1 (by rw [map_add (f := _), L.cj_cj, add_comm])
    have hs' : s ∉ 𝒪[F] := fun h' => hb' ⟨⟨s, h'⟩, hs.symm⟩
    obtain ⟨y, hy⟩ := not_forall.1 fun h' => hs' ((hψ s).1 h')
    let v : UU := ⟨(algebraMap F E y * b) • e a, hsm _ (L.O.mul_mem (hO y) hb) _ (heU a)⟩
    refine ⟨v, ψ (s * y), hy, fun u => ?_⟩
    have h2 : t * nrm (u + v + h) - t * nrm (u + v)
        = s * y + (t * nrm (u + h) - t * nrm u) := by
      apply hinj
      have h3 : hf L Hm v h = algebraMap F E y * b * L.cj z := by
        rw [hz, cj_hf L Hm hH.1]
        exact hf_smul_left L Hm _ _ _
      have h3' : hf L Hm h v = algebraMap F E y * L.cj b * z := by
        rw [← cj_hf L Hm hH.1, h3]
        simp only [map_mul, AlgEquiv.commutes, L.cj_cj]
      simp only [map_mul, AlgEquiv.commutes, L.cj_cj] at hs
      simp only [map_sub, map_add (algebraMap F E), map_mul, hnrm, hs, hf_add_left, hf_add_right,
        h3, h3']
      ring
    have h4 : (u : Fin n → E) + v + h - (u + v) = u + h - u := by abel
    simp only [map_mul, Submodule.coe_add]
    rw [mul_mul_mul_comm, GaussSum.mul_conj_eq ψ hψ1, GaussSum.mul_conj_eq χ hχ1,
      mul_mul_mul_comm, GaussSum.mul_conj_eq ψ hψ1, GaussSum.mul_conj_eq χ hχ1, h2, h4,
      AddChar.map_add_eq_mul, mul_assoc]

end GlobalTheory.HL.GaussSummand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordExist

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

noncomputable def linL (H : HermSp M V) (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' a b := H.h_add_left a b y
  map_smul' a x := H.h_smul_left a x y

lemma h_sum_left (H : HermSp M V) {n : ℕ} (c : Fin n → E) (b : Fin n → V) (y : V) :
    H.h (∑ i, c i • b i) y = ∑ i, c i * H.h (b i) y := by
  show linL H y (∑ i, c i • b i) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

lemma hf_eq (H : HermSp M V) {n : ℕ} (b : Fin n → V) (c d : Fin n → E) :
    hf M.L (Matrix.of fun i j => H.h (b i) (b j)) c d = H.h (∑ i, c i • b i) (∑ j, d j • b j) := by

  have hr : ∀ (x : V) (d : Fin n → E), H.h x (∑ j, d j • b j) = ∑ j, M.L.cj (d j) * H.h x (b j) := by
    intro x d
    set_option synthInstance.maxHeartbeats 100000 in
      rw [H.h_herm, h_sum_left, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← H.h_herm]
  rw [h_sum_left]
  unfold GlobalTheory.HL.hf
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  ring

lemma hf_basis (H : HermSp M V) {n : ℕ} (b : Module.Basis (Fin n) E V) (x y : V) :
    hf M.L (Matrix.of fun i j => H.h (b i) (b j)) (b.equivFun x) (b.equivFun y) = H.h x y := by
  rw [hf_eq, b.sum_equivFun, b.sum_equivFun]

lemma nontriv (L : LocE F E) : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)

lemma hermND (H : HermSp M V) {n : ℕ} (b : Module.Basis (Fin n) E V) :
    IsHermND M.L (Matrix.of fun i j => H.h (b i) (b j)) := by
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.HL.IsHerm GlobalTheory.HL.cT
    ext i j
    exact (H.h_herm (b j) (b i)).symm
  · have := M.L.free
    have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
    set G : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => H.h (b i) (b j) with hGdef
    have hvec : ∀ (v : Fin n → E) j, (Matrix.vecMul v G) j = H.h (∑ i, v i • b i) (b j) := by
      intro v j
      rw [h_sum_left]
      simp only [Matrix.vecMul, dotProduct, hGdef, Matrix.of_apply]
    have hright : ∀ x y : V, H.h x y = ∑ j, M.L.cj (b.repr y j) * H.h x (b j) := by
      intro x y
      conv_lhs => rw [← b.sum_repr y]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [H.h_herm, h_sum_left, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← H.h_herm]

    have hinj : Function.Injective (Matrix.vecMulLinear G) := by
      intro v v' hvv
      have hvv' : Matrix.vecMul v G = Matrix.vecMul v' G := hvv
      have hd : ∀ j, (Matrix.vecMul (v - v') G) j = 0 := by
        intro j
        rw [Matrix.sub_vecMul, hvv', sub_self]
        rfl
      have hx : ∑ i, (v - v') i • b i = 0 := by
        apply H.nondeg
        intro y
        rw [hright]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← hvec, hd, mul_zero]
      have h0 := Fintype.linearIndependent_iff.mp b.linearIndependent (v - v') hx
      funext i
      exact sub_eq_zero.mp (h0 i)

    have hsurj : Function.Surjective (Matrix.vecMulLinear G) := by
      have h2 : Function.Injective ((Matrix.vecMulLinear G).restrictScalars F) := hinj
      exact LinearMap.injective_iff_surjective.mp h2
    exact (Matrix.isUnit_iff_isUnit_det G).mp (Matrix.vecMul_surjective_iff_isUnit.mp hsurj)

lemma not_field (L : LocE F E) (g : SplitG L) : ¬ IsField E := by
  intro hE
  have hx : g.e.symm (1, 0) ≠ 0 := by
    intro h0
    have h1 := congrArg g.e h0
    simp at h1
  obtain ⟨x', hx'⟩ := hE.mul_inv_cancel hx
  have hxy : g.e.symm (1, 0) * g.e.symm (0, 1) = 0 := by
    rw [← map_mul]
    simp
  have hy : g.e.symm (0, 1) = 0 := by
    calc g.e.symm (0, 1) = (x' * g.e.symm (1, 0)) * g.e.symm (0, 1) := by
          rw [mul_comm x', hx', one_mul]
      _ = 0 := by rw [mul_assoc, hxy, mul_zero]
  have h1 := congrArg g.e hy
  simp at h1

lemma gram_eq {H : HermSp M V} {r : ℕ} (A : LocNG.FrameD H r) (a b : Fin (r + 1)) :
    H.h (A.f a) (A.f b) = if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E A.T else 0 := by
  split_ifs with hab
  · rw [hab.1, hab.2]
    exact A.h_zz
  · exact A.h_iso a b (not_and_or.mp hab)

lemma dual_eq {H : HermSp M V} {r : ℕ} (A : LocNG.FrameD H r) (a : Fin (r + 1)) (j : Fin r) :
    H.h (A.f a) (A.es j) = if a = j.castSucc then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    rw [if_neg (Fin.castSucc_lt_last j).ne', H.h_herm, A.h_sz, map_zero]
  | cast i =>
    rw [A.h_es i j]
    simp only [Fin.castSucc_inj]

lemma unit_of {T : F} (hT : T ∈ 𝒪[F]) (u : 𝒪[F]) (h : (u : F) * T = 1) :
    ∃ v : (𝒪[F])ˣ, ((v : 𝒪[F]) : F) = T := by
  refine ⟨⟨⟨T, hT⟩, u, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    show T * (u : F) = 1
    rw [mul_comm]
    exact h
  · apply Subtype.ext
    show (u : F) * T = 1
    exact h

end

theorem exists_coord : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∃ S : Frames M.L r k, Nonempty (Coord P S) := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r k P hrank hrel
  have := hOK.loc
  have : Nontrivial E := nontriv M.L
  have := H.free
  have := H.fin
  unfold LocNG.FPair.RelG LocNG.FPair.IsPoint LocNG.FPair.NormsOK at hrel
  obtain ⟨-, -, hG, -, -, ⟨w, hw⟩, hAT, hA0, hBT, hB0, hsp⟩ := hrel

  obtain ⟨ϖ, hϖ, hϖs⟩ : ∃ ϖ : 𝒪[F], Irreducible ϖ ∧ ∀ g, M.split = some g → ϖ = g.q := by
    cases hs : M.split with
    | none =>
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
      exact ⟨ϖ, hϖ, fun g hg => by cases hg⟩
    | some g =>
      exact ⟨g.q, g.q_irr, fun g' hg => by cases hg; rfl⟩
  let bs : Module.Basis (Fin (k + 2 * r + 1)) E V := Module.finBasisOfFinrankEq E V hrank
  have hZ : (Matrix.of fun a c => hf M.L (Matrix.of fun i j => H.h (bs i) (bs j))
      (bs.equivFun (P.B.f c)) (bs.equivFun (P.A.f a))) = H.Zhat P.A.f P.B.f := by
    ext a c
    simp only [Matrix.of_apply, hf_basis]
    rfl
  have hD1 : lead (H.Zhat P.A.f P.B.f) (Fin.last (r + 1)) = H.Dl P.A.f P.B.f (r + 1) := by
    unfold GlobalTheory.HL.lead HermSp.Dl
    rw [dite_eq_left le_rfl]
  have hD0 : lead (H.Zhat P.A.f P.B.f) (Fin.last r).castSucc = H.Dl P.A.f P.B.f r := by
    unfold GlobalTheory.HL.lead HermSp.Dl
    rw [dite_eq_left (Nat.le_succ r)]
  have hG' := hG
  unfold LocNG.FPair.Gv HermSp.Gdet HermSp.normE at hG'
  rw [← hD1, ← hD0, ← hZ] at hG'
  let S : Frames M.L r k :=
    { ϖ := ϖ
      ϖ_irr := hϖ
      Hm := Matrix.of fun i j => H.h (bs i) (bs j)
      herm := hermND H bs
      T := Units.mk0 P.A.T hA0
      T' := Units.mk0 P.B.T hB0
      f := fun a => bs.equivFun (P.A.f a)
      f' := fun a => bs.equivFun (P.B.f a)
      es := fun j => bs.equivFun (P.A.es j)
      es' := fun j => bs.equivFun (P.B.es j)
      gram := fun a c => by
        rw [hf_basis, gram_eq]
        rfl
      gram' := fun a c => by
        rw [hf_basis, gram_eq]
        rfl
      dual := fun a j => by rw [hf_basis, dual_eq]
      dual' := fun a j => by rw [hf_basis, dual_eq]
      iso := fun i j => by rw [hf_basis, P.A.h_ss]
      iso' := fun i j => by rw [hf_basis, P.B.h_ss]
      w := w
      relevant := fun a c => by
        rw [hf_basis, ← hw a c]
        have hsq : ((-1 : E) ^ (r - (c : ℕ))) * (-1) ^ (r - (c : ℕ)) = 1 := by
          rw [← mul_pow]
          simp
        show H.h (P.B.f c) (P.A.f a) =
          (-1) ^ (r - (c : ℕ)) * H.h (P.B.f c) (P.A.f a) * (-1) ^ (r - (c : ℕ))
        linear_combination (-(H.h (P.B.f c) (P.A.f a))) * hsq
      G_ne := hG'
      gg := M.split.isSome
      gg_ok := by
        intro hgg
        obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hgg
        obtain ⟨⟨u, v, hu, hv⟩, -⟩ := hsp g hg
        exact ⟨not_field M.L g, unit_of hAT u hu, unit_of hBT v hv⟩ }
  refine ⟨S, ⟨{ e := bs.equivFun
                h_eq := fun x y => hf_basis H bs x y
                f_eq := fun a => rfl
                f'_eq := fun a => rfl
                es_eq := fun a => rfl
                es'_eq := fun a => rfl
                T_eq := rfl
                T'_eq := rfl
                gg_none := fun h => ?_
                gg_some := fun g hg => ⟨?_, hϖs g hg⟩ }⟩⟩
  · show M.split.isSome = false
    rw [h]
    rfl
  · show M.split.isSome = true
    rw [hg]
    rfl

end GlobalTheory.HL.CoordExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumPiProdEnnreal
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem tsum_pi_prod_ennreal : ∀ {ι : Type} [Fintype ι] {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞),
    ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  intro ι _
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞),
      ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y) ?_ ?_ ?_ ι
  · intro α β _ e h X φ
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have h1 := h (X := fun a => X (e a)) (fun a => φ (e a))
    rw [← (Equiv.piCongrLeft X e).tsum_eq]
    calc ∑' x : ∀ a, X (e a), ∏ b, φ b (Equiv.piCongrLeft X e x b)
        = ∑' x : ∀ a, X (e a), ∏ a, φ (e a) (x a) := by
          congr 1; ext x
          rw [← Fintype.prod_equiv e (fun a => φ (e a) (Equiv.piCongrLeft X e x (e a)))
            (fun b => φ b (Equiv.piCongrLeft X e x b)) (fun _ => rfl)]
          simp only [Equiv.piCongrLeft_apply_apply]
      _ = ∏ a, ∑' y, φ (e a) y := h1
      _ = ∏ b, ∑' y, φ b y := Fintype.prod_equiv e _ _ (fun _ => rfl)
  · intro X φ
    simp
  · intro α _ h X φ
    rw [← (Equiv.piOptionEquivProd (β := X)).symm.tsum_eq, Fintype.prod_option]
    rw [← h (X := fun a => X (some a)) (fun a => φ (some a))]
    rw [← ENNReal.tsum_mul_right]
    simp only [Fintype.prod_option]
    rw [ENNReal.tsum_prod']
    congr 1; ext y
    rw [← ENNReal.tsum_mul_left]
    rfl

end GlobalTheory.HL
end

