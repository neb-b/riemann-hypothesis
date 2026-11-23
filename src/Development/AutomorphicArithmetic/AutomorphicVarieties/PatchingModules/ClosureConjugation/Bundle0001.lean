module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.ComplOddPart
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

section aux

variable {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] (Φ : OddForm B N)

private theorem ev_alg (b : B) : (algebraMap B Φ.Ext b).ev = b := by
  rw [Algebra.algebraMap_eq_smul_one, OddForm.ev_smul, OddForm.ev_one, mul_one]

private theorem od_alg (b : B) : (algebraMap B Φ.Ext b).od = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, OddForm.od_smul, OddForm.od_one, smul_zero]

private theorem mem_one_iff (z : Φ.Ext) : z ∈ (1 : Submodule B Φ.Ext) ↔ z.od = 0 := by
  rw [Submodule.mem_one]
  refine ⟨?_, fun h => ⟨z.ev, OddForm.ext (ev_alg Φ _) (by rw [od_alg, h])⟩⟩
  rintro ⟨b, rfl⟩
  exact od_alg Φ b

private def oddPart : Submodule B Φ.Ext where
  carrier := {z | z.ev = 0}
  add_mem' := fun {x y} (hx : x.ev = 0) (hy : y.ev = 0) => show (x + y).ev = 0 by
    rw [OddForm.ev_add, hx, hy, add_zero]
  zero_mem' := rfl
  smul_mem' := fun c x (hx : x.ev = 0) => show (c • x).ev = 0 by
    rw [OddForm.ev_smul, hx, mul_zero]

private theorem mem_oddPart (z : Φ.Ext) : z ∈ oddPart Φ ↔ z.ev = 0 := Iff.rfl

private theorem compl_oddPart : _root_.IsCompl (1 : Submodule B Φ.Ext) (oddPart Φ) := by
  refine ⟨Submodule.disjoint_def.2 fun z h1 h2 => ?_, codisjoint_iff.2 (eq_top_iff.2 fun z _ => ?_)⟩
  · exact OddForm.ext ((mem_oddPart Φ z).1 h2) ((mem_one_iff Φ z).1 h1)
  · refine Submodule.mem_sup.2 ⟨Φ.el z.ev 0, (mem_one_iff Φ _).2 rfl, Φ.el 0 z.od, rfl, ?_⟩
    apply OddForm.ext
    · change z.ev + 0 = z.ev
      simp
    · change 0 + z.od = z.od
      simp

end aux

private theorem oB_eq_iff {n a : ℕ} (h1 : 1 ≤ a) (h2 : a < n) (i j : Fin n) :
    oB n a i = oB n a j ↔ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) := by
  unfold oB
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] <;> omega

theorem UpperTheory.V.Pa.gr_E :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} [Module.Finite B E] (a : ℕ) (T : TrInv B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F) (U : T.Units (Fin n) (oB n a)), 1 ≤ a → a < n → RingHom.ker (algebraMap B F) = maximalIdeal B → (∀ y, r (T.st y) = (r y)ᵀ) → (∀ i, r (U.x i) = single (oB n a i) i 1) → (∀ y, r y ∈ Ev F F n a) → Nonempty (GrAlg T n a r U.ep) := by
  intro B E F _ _ _ _ _ _ n _ a T r U h1 h2 hker hst hx hev
  let p : Fin n := ⟨0, by omega⟩
  let q : Fin n := ⟨n - 1, by omega⟩
  have hpq : p ≠ q := fun h => by
    have := congrArg Fin.val h
    simp only [p, q] at this
    omega
  have ho : ∀ i, oB n a i = p ∨ oB n a i = q := fun i => by
    unfold oB
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hp : oB n a p = p := by
    unfold oB
    rw [if_pos (show 0 < a by omega)]
  have hq : oB n a q = q := by
    unfold oB
    rw [if_neg (show ¬ (n - 1 < a) by omega)]
  have h0 : ∀ y i j, oB n a i ≠ oB n a j → r y i j = 0 := fun y i j h =>
    (Submodule.mem_bot F).1 ((hev y i j).2 fun h' => h ((oB_eq_iff h1 h2 i j).2 h'))
  obtain ⟨φ, hφ, hφst, -⟩ := vr_hom T (oB n a) U p q hpq ho
  obtain ⟨hinj, hrange⟩ := vr_range T (oB n a) U p q hpq ho
  obtain ⟨hred, hle⟩ := vr_reduction T (oB n a) U r p q hst hx h0
  have hle' := hle hp hq hpq
  rw [hker] at hle'
  have hφe : (φ : E → _) = U.vr p q := funext hφ
  haveI : Module.Finite B (corner B (U.ep p) (U.ep q)) := Module.Finite.range _
  have hv : ∀ y y' k l, U.x k * y * T.st (U.x l) = U.x k * y' * T.st (U.x l) → φ y k l = φ y' k l :=
    fun y y' k l h => by
      rw [hφ, hφ]
      simp only [TrInv.Units.vr, Matrix.of_apply, h]
  have ha : ∀ i, U.x i * U.ep i = U.x i := fun i => by
    conv_lhs => rw [← U.x_mem i, mul_assoc, (U.coi.idem i).eq]
    exact U.x_mem i
  have hd : ∀ i, U.ep i * T.st (U.x i) = T.st (U.x i) := fun i => by
    rw [← U.st_ep i, ← T.st_mul, ha]
  refine ⟨{ AA := (U.oddForm p q).Ext
            fin := inferInstance
            inj := fun b b' h => ?_
            N := oddPart _
            compl := compl_oddPart _
            mul_mem := fun y hy z hz => ?_
            typeI := fun h => absurd h h2.ne
            φ := φ
            φ_inj := hφe ▸ hinj
            range := fun Y => ?_
            st := hφst
            φ_ep := fun i => ?_
            red := fun y i j b h => ?_ }⟩
  · rw [← ev_alg (U.oddForm p q) b, h, ev_alg]
  · rw [mem_oddPart] at hy hz
    refine ⟨(U.oddForm p q).be y.od z.od, hle' (Ideal.subset_span ⟨_, _, rfl⟩), OddForm.ext ?_ ?_⟩
    · rw [ev_alg, OddForm.ev_mul, hy, zero_mul, zero_add]
    · rw [od_alg, OddForm.od_mul, hy, hz, zero_smul, zero_smul, add_zero]
  · rw [hφe, hrange]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [mem_one_iff, mem_oddPart, Ne, oB_eq_iff h1 h2]
  · ext1 k l
    by_cases hk : k = i
    · subst hk
      by_cases hl : l = k
      · subst hl
        rw [hv (U.ep l) 1 l l (by rw [ha, mul_one]), map_one, one_apply_eq, single_apply_same]
      · have e : U.ep k * U.ep l = 0 := U.coi.ortho (Ne.symm hl)
        rw [hv (U.ep k) 0 k l (by rw [← hd l, mul_assoc, ← mul_assoc (U.ep k), e]; simp), map_zero,
          single_apply_of_col_ne _ _ (Ne.symm hl), Matrix.zero_apply]
    · have e : U.ep k * U.ep i = 0 := U.coi.ortho hk
      rw [hv (U.ep i) 0 k l (by rw [← ha k, mul_assoc (U.x k), e]; simp), map_zero,
        single_apply_of_row_ne (Ne.symm hk), Matrix.zero_apply]
  · rw [← hred y i j, ← hφ]
    have e : φ y i j = (φ y i j - algebraMap B _ b) + algebraMap B _ b := (sub_add_cancel _ _).symm
    rw [e, OddForm.ev_add, (mem_oddPart _ _).1 h, ev_alg, zero_add]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.EpsEq
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.eps_eq :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ g : G.G₀, P.f (G.frame.eps O B g : Bˣ) = ((G0.frame.eps ℤ_[l] x.A (h.p₀ g) : x.Aˣ) : x.A) ∧ h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P g
  have hl : (l : x.K) = 0 := by
    by_contra hn
    obtain ⟨p, hp⟩ := CharP.exists x.K
    have hpp : p.Prime := CharP.char_is_prime x.K p
    have hne : p ≠ l := by rintro rfl; exact hn (CharP.cast_eq_zero _ _)
    have h6 : IsUnit ((p : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => hne ?_)
      rw [PadicInt.norm_int_lt_one_iff_dvd] at hlt
      exact ((Nat.prime_dvd_prime_iff_eq Fact.out hpp).1 (by exact_mod_cast hlt)).symm
    have h8 := h6.map (algebraMap ℤ_[l] x.K)
    rw [map_intCast, Int.cast_natCast, CharP.cast_eq_zero] at h8
    exact not_isUnit_zero h8
  have hA : (l : x.A) = 0 := by rw [← map_natCast (PowerSeries.C (R := x.K)), hl, map_zero]
  have key : ∀ φ : ℤ_[l] →+* x.A, ∀ a, φ a = (a.zmodRepr : x.A) := fun φ a => by
    have h1 := PadicInt.sub_zmodRepr_mem a
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 := congrArg φ hc
    rw [map_mul, map_natCast, hA, mul_zero, map_sub, map_natCast] at h2
    exact sub_eq_zero.1 h2.symm
  refine ⟨?_, Subtype.ext ?_⟩
  · have e1 := key (P.f.toRingHom.comp ((algebraMap O B).comp (algebraMap ℤ_[l] O))) (G.ε g : ℤ_[l])
    have e2 := key ((algebraMap ℤ_[l] x.A).comp (algebraMap ℤ_[l] ℤ_[l])) (G0.ε (h.p g) : ℤ_[l])
    rw [h.ε] at e2
    refine e1.trans (e2.symm.trans ?_)
    rw [← h.ε]; rfl
  · show h.p (G.c * g * G.c⁻¹) = G0.c * h.p g * G0.c⁻¹
    rw [map_mul, map_mul, map_inv, h.c]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.FSurj
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.f_surj :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), Function.Surjective P.f ∧ IsLocalHom P.f.toRingHom := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P
  have hK : IsCO O x.K := by
    refine IsCO.mk ?_ ?_ ?_
    · rw [IsLocalRing.maximalIdeal_eq_bot]
      infer_instance
    · constructor
      intro a ha
      by_contra hna
      have hm : a ∈ maximalIdeal O := hna
      have hker : RingHom.ker (algebraMap O x.K) = maximalIdeal O :=
        eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ P.surj)
      have h0 : algebraMap O x.K a = 0 := by
        rw [← RingHom.mem_ker, hker]
        exact hm
      rw [h0] at ha
      exact not_isUnit_zero ha
    · intro y
      obtain ⟨a, rfl⟩ := P.surj y
      exact ⟨a, by rw [sub_self]; exact Ideal.zero_mem _⟩
  have hA : IsCO O x.A := co_mvps O x.K Unit
  have hs : P.s ∈ maximalIdeal B := by
    rw [← res_eq_zero_iff O B, ← res_map P.f, P.f_s, res_eq_zero_iff,
      PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.subset_span rfl
  have hsurj : Function.Surjective P.f := by
    apply co_surj O B x.A P.f
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hm := Ideal.mem_map_of_mem P.f hs
    rw [P.f_s] at hm
    exact Ideal.mem_sup_left hm
  exact ⟨hsurj, IsLocalHom.of_surjective P.f.toRingHom hsurj⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrI
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.gr_I :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} (T : TrInv B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F) (U : T.Units (Fin n) (oB n n)), 1 ≤ n → (∀ y, r (T.st y) = (r y)ᵀ) → (∀ i, r (U.x i) = single (oB n n i) i 1) → Nonempty (GrAlg T n n r U.ep) := by
  intro B E F _ _ _ _ _ _ n T r U hn hr hx
  have ho : ∀ i : Fin n, oB n n i = ⟨0, by omega⟩ := fun i => Fin.ext (by simp [oB, i.isLt])
  obtain ⟨φ, hφ, hst, -⟩ := units_one_block T (oB n n) U ⟨0, by omega⟩ ho
  have hU := units_basic T (oB n n) U
  have hxe : ∀ i' i : Fin n, U.x i' * U.ep i = if i' = i then U.x i' else 0 := by
    intro i' i
    conv_lhs => rw [← U.x_mem i']
    split_ifs with h
    · subst h
      rw [mul_assoc, (U.coi.idem i').eq, U.x_mem]
    · rw [mul_assoc, U.coi.ortho h, mul_zero]
  have hone : (1 : Submodule B B) = ⊤ :=
    eq_top_iff.2 fun x _ => Submodule.mem_one.2 ⟨x, rfl⟩
  refine ⟨@GrAlg.mk B E F _ _ _ _ _ _ T n n r U.ep B _ _ inferInstance (fun a b h => h) ⊥
    ?_ ?_ (fun _ => rfl) φ.toAlgHom φ.injective ?_ hst ?_ ?_⟩
  · rw [hone]
    exact isCompl_top_bot
  · intro y hy z hz
    rw [Submodule.mem_bot] at hy
    subst hy
    exact ⟨0, zero_mem _, by simp⟩
  · intro Y
    constructor
    · intro _
      intro i j
      refine ⟨fun _ => by rw [hone]; trivial, fun h => absurd ⟨fun _ => j.isLt, fun _ => i.isLt⟩ h⟩
    · intro _
      exact φ.surjective Y
  · intro i
    show φ (U.ep i) = _
    ext i' j'
    rw [hφ, hxe]
    split_ifs with h1
    · subst h1
      by_cases h2 : i' = j'
      · subst h2
        rw [U.x_st, U.tr_ep]
        simp [Matrix.single_apply]
      · rw [hU.1 i' j' h2, map_zero]
        simp [Matrix.single_apply, h2, Ne.symm h2]
    · simp [Matrix.single_apply, Ne.symm h1]
  · intro y i j b h
    rw [Submodule.mem_bot, sub_eq_zero] at h
    change φ y i j = b at h
    rw [← h, hφ]
    have he0 : r (U.ep ⟨0, by omega⟩) = single ⟨0, by omega⟩ ⟨0, by omega⟩ 1 := by
      have h0 := U.x_base ⟨0, by omega⟩
      rw [ho] at h0
      rw [← h0, hx, ho]
    have hk := hU.2.2.2.2.1 i j y (by rw [ho, ho])
    have hr2 := congrArg (fun M => M ⟨0, by omega⟩ ⟨0, by omega⟩) (congrArg r hk)
    simp only [map_mul, map_smul, hr, hx, ho, he0] at hr2
    simp [Matrix.mul_apply, Matrix.single_apply, Algebra.smul_def] at hr2
    rw [hr2]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrSs
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.gr_ss :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} {a : ℕ} {T : TrInv B E} {r : E →ₐ[B] Matrix (Fin n) (Fin n) F} {ep : Fin n → E} (g : GrAlg T n a r ep) (κ : Type) [Field κ] [Algebra B κ] (s : B), algebraMap B κ s ≠ 0 → s ∈ Module.annihilator B g.N → IsSemisimpleRing (κ ⊗[B] E) := by
  intro B E F _ _ _ _ _ _ n a T r ep g κ _ _ s hs hann
  classical
  let M : Fin n → Fin n → Matrix (Fin n) (Fin n) g.AA :=
    fun i k => Matrix.single i k (if ((i : ℕ) < a ↔ (k : ℕ) < a) then 1 else 0)
  have hM : ∀ i k, ∃ x : E, g.φ x = M i k := by
    intro i k
    rw [← Set.mem_range, g.range]
    intro p q
    refine ⟨fun _ => ?_, fun hpq => ?_⟩
    · simp only [M, Matrix.single_apply]
      split_ifs
      · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · exact zero_mem _
      · exact zero_mem _
    · simp only [M, Matrix.single_apply]
      split_ifs with h1 h2
      · obtain ⟨rfl, rfl⟩ := h1
        exact absurd h2 hpq
      · exact zero_mem _
      · exact zero_mem _
  choose e he using hM
  have hmul : ∀ i k l : Fin n, ((i : ℕ) < a ↔ (k : ℕ) < a) → ((k : ℕ) < a ↔ (l : ℕ) < a) →
      e i k * e k l = e i l := by
    intro i k l hik hkl
    apply g.φ_inj
    rw [map_mul, he, he, he]
    simp only [M, if_pos hik, if_pos hkl, if_pos (hik.trans hkl), Matrix.single_mul_single_same,
      mul_one]
  have hzero : ∀ i k l m : Fin n, k ≠ l → e i k * e l m = 0 := by
    intro i k l m hkl
    apply g.φ_inj
    rw [map_mul, he, he, map_zero]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hkl _
  have hcross : ∀ i k : Fin n, ¬((i : ℕ) < a ↔ (k : ℕ) < a) → e i k = 0 := by
    intro i k hik
    apply g.φ_inj
    rw [he, map_zero]
    simp only [M, if_neg hik, Matrix.single_zero]
  have hsum : ∑ i, e i i = 1 := by
    apply g.φ_inj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp only [he, M, iff_self, if_true]
    ext p q
    rw [Matrix.sum_apply]
    simp only [Matrix.single_apply]
    by_cases hpq : p = q
    · subst hpq
      simp
    · rw [Matrix.one_apply_ne hpq]
      exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => hpq (h.1.symm.trans h.2)))
  have hdec : ∀ y : E, ∃ b : Fin n → Fin n → B, s • y = ∑ i, ∑ k, b i k • e i k := by
    intro y
    have hent : ∀ i k, ∃ c : B, s • g.φ y i k = c • (if ((i : ℕ) < a ↔ (k : ℕ) < a) then 1 else 0) := by
      intro i k
      obtain ⟨h1, h2⟩ := (g.range (g.φ y)).mp ⟨y, rfl⟩ i k
      by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
      · obtain ⟨c, hc⟩ := Submodule.mem_one.mp (h1 hik)
        refine ⟨s * c, ?_⟩
        rw [if_pos hik, ← hc, Algebra.algebraMap_eq_smul_one, smul_smul]
      · refine ⟨0, ?_⟩
        rw [if_neg hik, smul_zero]
        have := (Module.mem_annihilator.mp hann) ⟨_, h2 hik⟩
        simpa using congrArg Subtype.val this
    choose c hc using hent
    refine ⟨c, g.φ_inj ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum]
    ext p q
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, he, M, Matrix.smul_apply, Matrix.sum_apply, Matrix.single_apply]
    rw [hc, Finset.sum_eq_single p (fun i _ hi => Finset.sum_eq_zero (fun k _ => by
        rw [if_neg (fun h => hi h.1), smul_zero])) (by simp),
      Finset.sum_eq_single q (fun k _ hk => by rw [if_neg (fun h => hk h.2), smul_zero]) (by simp)]
    simp
  let bf : Fin n → Bool := fun i => decide ((i : ℕ) < a)
  let cl : Fin n → Set.range bf := Set.rangeFactorization bf
  have hcl : ∀ i k : Fin n, cl i = cl k ↔ ((i : ℕ) < a ↔ (k : ℕ) < a) := by
    intro i k
    simp only [cl, bf, Set.rangeFactorization, Subtype.mk.injEq, decide_eq_decide]
  let d : Set.range bf → Type := fun t => {i : Fin n // cl i = t}
  haveI : ∀ t, Nonempty (d t) := fun t => by
    obtain ⟨i, hi⟩ := Set.rangeFactorization_surjective t
    exact ⟨⟨i, hi⟩⟩
  let ee : (t : Set.range bf) → d t → d t → κ ⊗[B] E := fun t i k => (1 : κ) ⊗ₜ[B] e i.1 k.1
  obtain ⟨j, hj⟩ := alghom_of_units (K := κ) (E := κ ⊗[B] E) d ee
    (fun t i k l => by
      simp only [ee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hmul _ _ _ ((hcl _ _).mp (i.2.trans k.2.symm)) ((hcl _ _).mp (k.2.trans l.2.symm))])
    (fun t i k l m hkl => by
      simp only [ee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hzero _ _ _ _ (fun h => hkl (Subtype.ext h)), TensorProduct.tmul_zero])
    (fun t u i k l m htu => by
      simp only [ee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hzero _ _ _ _ (fun h => htu (by rw [← k.2, ← l.2, h])), TensorProduct.tmul_zero])
    (by
      simp only [ee]
      rw [Fintype.sum_fiberwise cl (fun i => (1 : κ) ⊗ₜ[B] e i i), ← TensorProduct.tmul_sum, hsum,
        Algebra.TensorProduct.one_def])
  have hgen : ∀ i k : Fin n, (1 : κ) ⊗ₜ[B] e i k ∈ j.range := by
    intro i k
    by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · have hk : cl k = cl i := (hcl k i).mpr hik.symm
      exact (AlgHom.mem_range j).mpr
        ⟨Pi.single (cl i) (Matrix.single ⟨i, rfl⟩ ⟨k, hk⟩ 1), hj (cl i) ⟨i, rfl⟩ ⟨k, hk⟩⟩
    · rw [hcross i k hik, TensorProduct.tmul_zero]
      exact Subalgebra.zero_mem _
  have hone : ∀ y : E, (1 : κ) ⊗ₜ[B] y ∈ j.range := by
    intro y
    obtain ⟨b, hb⟩ := hdec y
    have h1 : (1 : κ) ⊗ₜ[B] y = (algebraMap B κ s)⁻¹ • ((1 : κ) ⊗ₜ[B] (s • y)) := by
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
        smul_eq_mul, inv_mul_cancel₀ hs]
    rw [h1, hb, TensorProduct.tmul_sum]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ (fun i _ => ?_)) _
    rw [TensorProduct.tmul_sum]
    refine Subalgebra.sum_mem _ (fun k _ => ?_)
    have h2 : (1 : κ) ⊗ₜ[B] (b i k • e i k) = (algebraMap B κ (b i k)) • ((1 : κ) ⊗ₜ[B] e i k) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    rw [h2]
    exact Subalgebra.smul_mem _ (hgen i k) _
  refine RingHom.isSemisimpleRing_of_surjective j.toRingHom ?_
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul u y =>
    obtain ⟨z, hz⟩ := (AlgHom.mem_range j).mp (hone y)
    refine ⟨u • z, ?_⟩
    show j (u • z) = _
    rw [map_smul, hz, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy =>
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, hw⟩ := hy
    exact ⟨z + w, by rw [map_add (f := _), hz, hw]⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatChi
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem characteristic_polynomial_compatibility {n : ℕ} {G B A Bh F E : Type} [Group G] [CommRing B] [CommRing A] [CommRing Bh] [CommRing F]
    [Ring E] [Algebra Bh E] [Algebra Bh F] (D : GDet n B G) (f : B →+* A) (g : B →+* Bh) (a : A →+* F)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (hD : D.map f = GDet.ofRep ρ)
    (hc : ∀ b, algebraMap Bh F (g b) = a (f b)) (ι : MonoidAlgebra Bh G →ₐ[Bh] E) (DE : Det n Bh E)
    (hp : DE.pull ι = (D.map g).toDet) (r : E →ₐ[Bh] Matrix (Fin n) (Fin n) F)
    (hr : ∀ s, r (ι (MonoidAlgebra.single s 1)) = (ρ s).map a) (z : MonoidAlgebra Bh G) :
    (DE.chi (ι z)).map (algebraMap Bh F) = (r (ι z)).charpoly := by
  have hc' : (algebraMap Bh F).comp g = a.comp f := RingHom.ext hc
  rw [← (d_pull DE ι).1 z, hp, (d_toDet _ z).1, ← ((d_gmap (D.map g)).2.2.1 (algebraMap Bh F) z).1,
    (d_gmap D).2.1, hc', ← (d_gmap D).2.1, hD, (d_gmap (GDet.ofRep ρ)).2.2.2, ← (d_toDet _ _).1,
    d_toDet_ofRep.1, (d_ofRep _ _ _).1]
  congr 1
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | single s b =>
    have : (MonoidAlgebra.single s b : MonoidAlgebra Bh G) = b • MonoidAlgebra.single s 1 := by simp
    rw [MonoidAlgebra.mapRingHom_single]
    conv_rhs => rw [this, map_smul, map_smul, hr]
    ext i j
    simp [GDet.repAlg, Algebra.smul_def]

theorem UpperTheory.V.Pa.hat_chi :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) → ∀ H : Hat h x u.D P.ker Bh (G.frame.eps O B), ∀ y, (H.DE.chi y).map (algebraMap Bh (FractionRing x.A)) = (H.r y).charpoly := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hc H y
  obtain ⟨z, rfl⟩ := H.surj y
  exact characteristic_polynomial_compatibility u.D P.f.toRingHom (algebraMap B Bh) (algebraMap x.A (FractionRing x.A)) (mat (x.ρ.comp h.p₀))
    P.maps.1 hc H.ι H.DE H.pull H.r H.r_ι z
end

