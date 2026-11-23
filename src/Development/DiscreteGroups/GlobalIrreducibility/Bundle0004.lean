module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0003
public import Development.DiscreteGroups.GlobalIrreducibility.LConvSepM

@[expose] public section

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def LDepth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, ∀ τ : FDRep ℂ (Gn g n),
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      fixed (cls σ).rep (KOne (w.adicCompletion E) (Fin (cls σ).1)) ≠ ⊥

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.InHCorner
section
noncomputable section
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] {m : ℕ}

theorem U_zero (c : Fin (m + 1)) : U c (0 : Fin (m + 1) → k) = 1 := Units.ext (colM_zero c)

theorem conj_U (j : ℕ) (hj : j + 1 < m + 1) (g : GL (Fin (m + 1)) k) (hg : InH (j + 1) g)
    (x : Fin (m + 1) → k) :
    g * U ⟨j + 1, hj⟩ x = U ⟨j + 1, hj⟩ (fun p => ∑ r, (if r < (⟨j + 1, hj⟩ : Fin (m + 1)) then
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p r else 0) * x r) * g := by
  set c : Fin (m + 1) := ⟨j + 1, hj⟩ with hc
  have hrow : ∀ q, (g : Matrix _ _ k) c q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) c q :=
    fun q => hg c q (fun h => lt_irrefl _ h.1)
  have hlow : ∀ p r : Fin (m + 1), ¬ p < c → r < c → (g : Matrix _ _ k) p r = 0 := fun p r hp hr => by
    rw [hg p r (fun h => hp (by rw [Fin.lt_def]; exact h.1)),
      Matrix.one_apply_ne (fun h => hp (by rw [h]; exact hr))]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  show (g : Matrix _ _ k) * colM c x = colM c _ * (g : Matrix _ _ k)
  ext p q
  simp only [colM, mul_add, add_mul, mul_one, one_mul, Matrix.add_apply]
  congr 1
  simp only [Matrix.mul_apply, Matrix.of_apply]
  conv_rhs => rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ c) h)]
  by_cases hq : q = c
  · rw [hq, hrow c, Matrix.one_apply_eq, mul_one]
    by_cases hp : p < c
    · rw [if_pos ⟨rfl, hp⟩]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : r < c
      · rw [if_pos ⟨rfl, hr⟩, if_pos hr]
      · rw [if_neg (fun h => hr h.2), if_neg hr]; simp
    · rw [if_neg (fun h => hp h.2)]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : r < c
      · rw [hlow p r hp hr, zero_mul]
      · rw [if_neg (fun h => hr h.2), mul_zero]
  · rw [hrow q, Matrix.one_apply_ne (Ne.symm hq), mul_zero]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg (fun h => hq h.1), mul_zero]

theorem decomp (j : ℕ) (hj : j < m + 1) (M : GL (Fin (m + 1)) k) (hM : InH (j + 1) M)
    (hrow : ∀ q, (M : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ⟨j, hj⟩ q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ⟨j, hj⟩ q) :
    ∃ y h, InH j h ∧ M = U ⟨j, hj⟩ y * h := by
  set jj : Fin (m + 1) := ⟨j, hj⟩ with hjj
  let y : Fin (m + 1) → k := fun p => (M : Matrix _ _ k) p jj
  refine ⟨y, U jj (-y) * M, ?_, ?_⟩
  · intro p q hpq
    show (colM jj (-y) * (M : Matrix (Fin (m + 1)) (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q = _
    rw [colM, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [Finset.sum_eq_single jj (fun r _ hr => by simp [hr]) (fun h => absurd (Finset.mem_univ jj) h)]
    rw [hrow q]
    by_cases hqj : q = jj
    · rw [hqj, Matrix.one_apply_eq, mul_one]
      by_cases hp : p < jj
      · rw [if_pos ⟨rfl, hp⟩, Matrix.one_apply_ne (ne_of_lt hp)]
        simp only [y, Pi.neg_apply]; ring
      · rw [if_neg (fun h => hp h.2), add_zero]
        by_cases hpe : p = jj
        · rw [hpe]; exact hrow jj
        · refine hM p jj (fun h => hp ?_)
          rw [Fin.lt_def]; rw [Fin.ext_iff] at hpe; simp [hjj] at h hpe ⊢; omega
    · rw [Matrix.one_apply_ne (fun h => hqj h.symm), mul_zero, add_zero]
      by_cases hpe : p = jj
      · rw [hpe]; exact hrow q
      · refine hM p q (fun h => hpq ⟨?_, ?_⟩)
        · rw [Fin.ext_iff] at hpe; simp [hjj] at hpe; omega
        · rw [Fin.ext_iff] at hqj; simp [hjj] at hqj; omega
  · rw [← mul_assoc, ← U_add, add_neg_cancel, U_zero, one_mul]

theorem InH_corner (g : GL (Fin m) k) : InH m (corner g) := by
  intro p q hpq
  rw [corner, val_emb₂, Matrix.reindex_apply, Matrix.submatrix_apply]
  induction p using Fin.addCases with
  | left a =>
    induction q using Fin.addCases with
    | left b => exact absurd ⟨by simp, by simp⟩ hpq
    | right b => simp [stdSum, Matrix.one_apply, Fin.ext_iff]; omega
  | right a =>
    induction q using Fin.addCases with
    | left b => simp [stdSum, Matrix.one_apply, Fin.ext_iff]; omega
    | right b =>
      have := Subsingleton.elim a b
      subst this
      simp [stdSum]

end DiscreteGroups.sglob.LConvKir
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvAltB
section
noncomputable section

open GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

theorem alt_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G) (N : ℕ)
    (hN : UnifAdm G K N) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)) (e : H →L[ℂ] H) (hKe' : ∀ κ ∈ K, π κ * e = e) (hee : e * e = e)
    (Y Y' : Submodule ℂ (H →L[ℂ] H))
    (hYs : Y ≤ Submodule.span ℂ (Set.range fun h => π h * e)) (heY : e ∈ Y)
    (hY1 : ∀ h, ∀ y ∈ Y, π h * y ∈ Y) (hYE : ∀ y ∈ Y, e * y ∈ Y)
    (hSm : ∀ y ∈ Y, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u * y = y)
    (hY'Y : Y' ≤ Y) (hY'G : ∀ h, ∀ y ∈ Y', π h * y ∈ Y') (hY'E : ∀ y ∈ Y', e * y ∈ Y') (heY' : e ∉ Y')
    (hmax : ∀ Z : Submodule ℂ (H →L[ℂ] H), Z ≤ Y → (∀ h, ∀ z ∈ Z, π h * z ∈ Z) → e ∉ Z → Y' ≤ Z → Z ≤ Y')
    (d : ℕ) (hd : N ^ 2 < d) (g : Fin d → G) :
    (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun i => e * π (g (σ i)) * e).prod) * e ∈ Y' := by
  let ρY : Representation ℂ G Y :=
    { toFun := fun h => (LinearMap.mulLeft ℂ (π h)).restrict (fun y hy => hY1 h y hy)
      map_one' := by
        refine LinearMap.ext fun y => Subtype.ext ?_
        show π 1 * (y : H →L[ℂ] H) = y
        rw [map_one, one_mul]
      map_mul' := by
        intro a b
        refine LinearMap.ext fun y => Subtype.ext ?_
        show π (a * b) * (y : H →L[ℂ] H) = π a * (π b * y)
        rw [map_mul, mul_assoc] }
  have hρY : ∀ h (y : Y), ((ρY h y : Y) : H →L[ℂ] H) = π h * y := fun h y => rfl
  let Y'' : Submodule ℂ Y := Y'.comap Y.subtype
  have hρY'' : ∀ h, Y'' ≤ Y''.comap (ρY h) := fun h y hy => hY'G h y hy
  let ρQ : Representation ℂ G (Y ⧸ Y'') :=
    { toFun := fun h => Y''.mapQ Y'' (ρY h) (hρY'' h)
      map_one' := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        show Submodule.Quotient.mk (ρY 1 y) = Submodule.Quotient.mk y
        rw [map_one]; rfl
      map_mul' := by
        intro a b
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        show Submodule.Quotient.mk (ρY (a * b) y) = Submodule.Quotient.mk (ρY a (ρY b y))
        rw [map_mul]; rfl }
  have hρQ : ∀ h (y : Y), ρQ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (ρY h y) := fun h y => rfl
  have hsm : IsSmooth ρQ := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
    obtain ⟨U, hUo, hU⟩ := hSm y y.2
    exact alt_isOpen_fix ρQ _ U hUo fun v hv => by
      rw [hρQ]; congr 1; exact Subtype.ext (hU v hv)
  have hmk0 : ∀ y : Y, (Submodule.Quotient.mk y : Y ⧸ Y'') = 0 ↔ (y : H →L[ℂ] H) ∈ Y' :=
    fun y => Submodule.Quotient.mk_eq_zero Y''
  have hirr : ρQ.IsIrreducible := by
    unfold Representation.IsIrreducible
    rw [isSimpleOrder_iff]
    refine ⟨⟨⊥, ⊤, fun hbt => heY' ?_⟩, fun a => ?_⟩
    · have h1 : (Submodule.Quotient.mk (⟨e, heY⟩ : Y) : Y ⧸ Y'') ∈ (⊥ : Subrepresentation ρQ).toSubmodule := by
        rw [hbt]; exact Submodule.mem_top
      exact (hmk0 _).mp ((Submodule.mem_bot ℂ).mp h1)
    · let Z : Submodule ℂ (H →L[ℂ] H) := (a.toSubmodule.comap Y''.mkQ).map Y.subtype
      have hZY : Z ≤ Y := by rintro _ ⟨y, _, rfl⟩; exact y.2
      have hZG : ∀ h, ∀ x ∈ Z, π h * x ∈ Z := by
        rintro h _ ⟨y, hy, rfl⟩
        exact ⟨ρY h y, a.apply_mem_toSubmodule h hy, rfl⟩
      have hY'Z : Y' ≤ Z := by
        intro x hx
        refine ⟨⟨x, hY'Y hx⟩, ?_, rfl⟩
        show Submodule.Quotient.mk _ ∈ a.toSubmodule
        rw [(hmk0 _).mpr hx]
        exact a.toSubmodule.zero_mem
      by_cases heZ : e ∈ Z
      · right
        apply Subrepresentation.toSubmodule_injective
        show a.toSubmodule = ⊤
        refine eq_top_iff.mpr fun q _ => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
        have hYZ : Y ≤ Z := hYs.trans (Submodule.span_le.mpr (by rintro _ ⟨h, rfl⟩; exact hZG h e heZ))
        obtain ⟨y', hy', hyy⟩ := hYZ y.2
        rw [← Subtype.ext hyy]
        exact hy'
      · left
        apply Subrepresentation.toSubmodule_injective
        show a.toSubmodule = ⊥
        refine eq_bot_iff.mpr fun q hq => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
        have := hmax Z hZY hZG heZ hY'Z ⟨y, hq, rfl⟩
        exact (Submodule.mem_bot ℂ).mpr ((hmk0 y).mpr this)
  obtain ⟨hfd, hfr⟩ := hN (Y ⧸ Y'') ρQ hsm hirr
  let f : G → (H →L[ℂ] H) := fun h => e * π h * e
  have hfY : ∀ a, ∀ y ∈ Y, f a * y ∈ Y := fun a y hy => by
    show e * π a * e * y ∈ Y
    rw [mul_assoc, mul_assoc]; exact hYE _ (hY1 a _ (hYE y hy))
  let TY : G → Module.End ℂ Y := fun a => (LinearMap.mulLeft ℂ (f a)).restrict (fun y hy => hfY a y hy)
  have hTY'' : ∀ a, Y'' ≤ Y''.comap (TY a) := fun a y hy => by
    show e * π a * e * (y : H →L[ℂ] H) ∈ Y'
    rw [mul_assoc, mul_assoc]; exact hY'E _ (hY'G a _ (hY'E _ hy))
  let T : G → Module.End ℂ (Y ⧸ Y'') := fun a => Y''.mapQ Y'' (TY a) (hTY'' a)
  have hfixmk : ∀ y : Y, e * (y : H →L[ℂ] H) = y → Submodule.Quotient.mk y ∈ fixed ρQ K := by
    intro y hy
    show ∀ κ : K, _
    intro κ
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [hρQ]; congr 1; apply Subtype.ext
    rw [hρY, ← hy, ← mul_assoc, hKe' κ κ.2]
  have hTW : ∀ a q, T a q ∈ fixed ρQ K := by
    intro a q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
    exact hfixmk (TY a y) (by show e * (e * π a * e * (y : H →L[ℂ] H)) = e * π a * e * y; simp only [← mul_assoc, hee])
  have := hfd
  let t : G → Module.End ℂ (fixed ρQ K) := fun a => (T a).restrict (fun q _ => hTW a q)
  have hdim : Module.finrank ℂ (Module.End ℂ (fixed ρQ K)) < d := by
    rw [Module.finrank_linearMap, ← sq]
    exact lt_of_le_of_lt (Nat.pow_le_pow_left hfr 2) hd
  have h0 := alt_std_eq_zero hdim fun i => t (g i)
  have key : ∀ (l : List G) (w : fixed ρQ K), (((l.map t).prod w : fixed ρQ K) : Y ⧸ Y'') = (l.map T).prod w := by
    intro l w
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      exact congrArg (T a) ih
  have key2 : ∀ (l : List G) (y : Y),
      (l.map T).prod (Submodule.Quotient.mk y) = Submodule.Quotient.mk ((l.map TY).prod y) := by
    intro l y
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]; rfl
  have key3 : ∀ (l : List G) (y : Y), (((l.map TY).prod y : Y) : H →L[ℂ] H) = (l.map f).prod * y := by
    intro l y
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.prod_cons, mul_assoc, ← ih]
      rfl
  let e' : Y := ⟨e, heY⟩
  have he'W : Submodule.Quotient.mk e' ∈ fixed ρQ K := hfixmk e' hee
  have h1 := congrArg (fun X : Module.End ℂ (fixed ρQ K) => ((X ⟨_, he'W⟩ : fixed ρQ K) : Y ⧸ Y'')) h0
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    LinearMap.zero_apply, ZeroMemClass.coe_zero] at h1
  have hsum : ∀ σ : Equiv.Perm (Fin d), (((List.ofFn fun i => t (g (σ i))).prod ⟨_, he'W⟩ : fixed ρQ K) : Y ⧸ Y'')
      = Y''.mkQ (((List.ofFn fun i => g (σ i)).map TY).prod e') := by
    intro σ
    rw [show (List.ofFn fun i => t (g (σ i))) = (List.ofFn fun i => g (σ i)).map t by rw [List.map_ofFn]; rfl,
      key, key2]
    rfl
  have h1' : Y''.mkQ (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((List.ofFn fun i => g (σ i)).map TY).prod e') = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine (Finset.sum_congr rfl fun σ _ => ?_).trans h1
    rw [map_smul, hsum]
  have h2 := (Submodule.Quotient.mk_eq_zero Y'').mp h1'
  have h3 : ((∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((List.ofFn fun i => g (σ i)).map TY).prod e' : Y) : H →L[ℂ] H) =
      (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun i => e * π (g (σ i)) * e).prod) * e := by
    rw [Submodule.coe_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Submodule.coe_smul, key3, smul_mul_assoc,
      show (List.ofFn fun i => e * π (g (σ i)) * e) = (List.ofFn fun i => g (σ i)).map f by rw [List.map_ofFn]; rfl]
  rw [← h3]
  exact h2

end DiscreteGroups.sglob.LConv
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvBigB
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] {m : ℕ}

def cornerHom : GL (Fin m) k →* GL (Fin (m + 1)) k :=
  (emb₂ k (stdSum (rfl : m + 1 = m + 1))).comp (MonoidHom.inl _ _)

theorem cornerHom_apply (g : GL (Fin m) k) : cornerHom g = corner g := rfl

def IsP (p : GL (Fin (m + 1)) k) : Prop :=
  ∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j

theorem mul_apply_last_of_isMirabolic {a b : GL (Fin (m + 1)) k} (ha : IsP a) (j : Fin (m + 1)) :
    ((a * b : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
      (b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := by
  rw [Units.val_mul, Matrix.mul_apply]
  calc ∑ c, (a : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c * (b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) c j
      = ∑ c, (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c * (b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) c j :=
        Finset.sum_congr rfl fun c _ => by rw [ha c]
    _ = _ := by rw [← Matrix.mul_apply, Matrix.one_mul]

theorem isMirabolic_mul {a b : GL (Fin (m + 1)) k} (ha : IsP a) (hb : IsP b) : IsP (a * b) := fun j =>
  (mul_apply_last_of_isMirabolic ha j).trans (hb j)

theorem isMirabolic_corner (g : GL (Fin m) k) : IsP (corner g) := corner_last g

theorem exists_eq_mul_corner {p : GL (Fin (m + 1)) k} (hp : IsP p) :
    ∃ u ∈ unipB k (Fin (m + 1)), ∃ h : GL (Fin m) k, p = u * corner h := by
  have hne : ∀ j : Fin m, Fin.last m ≠ j.castSucc := fun j => (Fin.castSucc_lt_last j).ne'
  set A : Matrix (Fin m) (Fin m) k := (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k).submatrix Fin.castSucc Fin.castSucc
  have he : ((-1 : k) ^ (m + m)) = 1 := by rw [← two_mul, pow_mul]; simp
  have hdet : (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k).det = A.det := by
    have hp' : ∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := hp
    rw [Matrix.det_succ_row _ (Fin.last m), Fin.sum_univ_castSucc]
    simp [hp', Matrix.one_apply, hne, Fin.succAbove_last, A, he]
  have hA : A.det ≠ 0 := by
    rw [← hdet]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 p.isUnit).ne_zero
  set h : GL (Fin m) k := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
  have hh : (h : Matrix (Fin m) (Fin m) k) = A := rfl
  refine ⟨p * corner h⁻¹, ?_, h, ?_⟩
  swap
  · rw [mul_assoc, ← cornerHom_apply, ← cornerHom_apply, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have hL : ∀ j, ((p * corner h⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := fun j =>
    (mul_apply_last_of_isMirabolic hp j).trans (corner_last _ j)
  have hB : ∀ i j : Fin m, ((p * corner h⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
      i.castSucc j.castSucc = (1 : Matrix (Fin m) (Fin m) k) i j := by
    intro i j
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, corner_last, Matrix.one_apply_ne (hne j)]
    simp only [corner_cs_cs, mul_zero, add_zero]
    rw [← h.mul_inv, Matrix.mul_apply, hh]
    rfl
  refine (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · induction i using Fin.lastCases with
    | last => rw [hL, Matrix.one_apply_ne hij.ne']
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last i).le)
      | cast j =>
        rw [hB, Matrix.one_apply_ne]
        intro e; subst e; exact lt_irrefl _ hij
  · induction i using Fin.lastCases with
    | last => rw [hL, Matrix.one_apply_eq]
    | cast i => rw [hB, Matrix.one_apply_eq]

section Agree

variable {ψ : AddChar k Circle} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {π₁ : Representation ℂ (GL (Fin (m + 1)) k) V₁} {π₂ : Representation ℂ (GL (Fin (m + 1)) k) V₂}
  {l₁ : Module.Dual ℂ V₁} {l₂ : Module.Dual ℂ V₂}

theorem agree_of_isP (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) {p : GL (Fin (m + 1)) k}
    (hp : IsP p) : l₁ (π₁ p v₁) = l₂ (π₂ p v₂) := by
  obtain ⟨u, hu, h, rfl⟩ := exists_eq_mul_corner hp
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hl₁ u hu, hl₂ u hu, hX h]

theorem agree_translate (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) {p : GL (Fin (m + 1)) k}
    (hp : IsP p) (g : GL (Fin m) k) : l₁ (π₁ (corner g) (π₁ p v₁)) = l₂ (π₂ (corner g) (π₂ p v₂)) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  exact agree_of_isP hl₁ hl₂ hX (isMirabolic_mul (isMirabolic_corner g) hp)

end Agree

end DiscreteGroups.sglob.LConv

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvSepF
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

theorem form_eq_zero_of_self {M : Type} [AddCommGroup M] [Module ℂ M] {B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ}
    (hh : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (hp : ∀ x, 0 ≤ (B x x).re) {z : M} (hz : B z z = 0)
    (x : M) : B z x = 0 := by
  by_contra ha
  have hn : 0 < Complex.normSq (B z x) := Complex.normSq_pos.2 ha
  have hxz : B x z = (starRingEnd ℂ) (B z x) := (hh z x).symm
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 2 * t * Complex.normSq (B z x) = (B x x).re + 1 :=
    ⟨((B x x).re + 1) / (2 * Complex.normSq (B z x)), by field_simp⟩
  have key := hp (x + ((-(t : ℂ)) * B z x) • z)
  have e1 : B (x + ((-(t : ℂ)) * B z x) • z) (x + ((-(t : ℂ)) * B z x) • z) =
      B x x + (-(t : ℂ)) * B z x * (starRingEnd ℂ) (B z x) +
        (starRingEnd ℂ) (-(t : ℂ) * B z x) * B z x := by
    simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, hz, hxz]
    ring
  have e2 : (B (x + ((-(t : ℂ)) * B z x) • z) (x + ((-(t : ℂ)) * B z x) • z)).re =
      (B x x).re - 2 * t * Complex.normSq (B z x) := by
    rw [e1]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_mul, map_neg,
      Complex.conj_ofReal, Complex.normSq_apply]
    ring
  linarith

theorem circle_conj_mul (z : Circle) : (starRingEnd ℂ) (z : ℂ) * z = 1 := by
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]

theorem conj_mul_self_re (z : ℂ) : ((starRingEnd ℂ) z * z).re = Complex.normSq z := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

theorem conj_psi (c : k) : (starRingEnd ℂ) ((ψ c : Circle) : ℂ) = ((ψ⁻¹ c : Circle) : ℂ) := by
  rw [AddChar.inv_apply', Circle.coe_inv_eq_conj]

theorem superDiag_inv {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) : superDiag u⁻¹ = -superDiag u := by
  have h := superDiag_mul ((unipB k (Fin m)).inv_mem hu) hu
  rw [inv_mul_cancel, superDiag_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem superDiag_conj {u n : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) (hn : n ∈ unipB k (Fin m)) :
    superDiag (u⁻¹ * n * u) = superDiag n := by
  have hu' := (unipB k (Fin m)).inv_mem hu
  rw [superDiag_mul ((unipB k (Fin m)).mul_mem hu' hn) hu, superDiag_mul hu' hn, superDiag_inv hu]
  ring

theorem delta_one {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) : (delta ψ K : GL (Fin m) k → ℂ) 1 = 1 := by
  have := delta_mul hK (unipB k (Fin m)).one_mem K.one_mem
  rw [mul_one, superDiag_one, AddChar.map_zero_eq_one, Circle.coe_one] at this
  exact this

theorem delta_ne_zero {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) : delta ψ K ≠ 0 := fun h => by
  have := delta_one hK
  rw [h] at this
  exact zero_ne_one this

theorem delta_eq_of_le {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (hK' : Good ψ K') (hle : K' ≤ K)
    (g : GL (Fin m) k) (hg : (delta ψ K' : GL (Fin m) k → ℂ) g ≠ 0) :
    (delta ψ K : GL (Fin m) k → ℂ) g = (delta ψ K' : GL (Fin m) k → ℂ) g := by
  obtain ⟨u, hu, κ, hκ, rfl⟩ : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K', g = u * κ := by
    by_contra h
    exact hg (delta_eq_zero h)
  rw [delta_mul hK hu (hle hκ), delta_mul hK' hu hκ]

theorem good_conj {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) : Good ψ (K.map (MulAut.conj u).toMonoidHom) := by
  have e : ((K.map (MulAut.conj u).toMonoidHom : Subgroup (GL (Fin m) k)) : Set (GL (Fin m) k)) =
      (fun y => u⁻¹ * y * u) ⁻¹' K := Set.ext fun _ => mem_conj
  have hc : Continuous fun κ : GL (Fin m) k => u * κ * u⁻¹ := by fun_prop
  refine ⟨?_, ?_, fun n hn hnK => ?_⟩
  · rw [e]
    exact hK.1.preimage (by fun_prop)
  · rw [Subgroup.coe_map]
    exact hK.2.1.image hc
  · rw [← superDiag_conj hu hn]
    exact hK.2.2 _ ((unipB k (Fin m)).mul_mem ((unipB k (Fin m)).mul_mem
      ((unipB k (Fin m)).inv_mem hu) hn) hu) (mem_conj.1 hnK)

end DiscreteGroups.sglob.LConv

end
end

