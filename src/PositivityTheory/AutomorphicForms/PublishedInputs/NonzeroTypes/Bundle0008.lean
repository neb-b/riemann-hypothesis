module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0004
public import Mathlib

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.LeviEigenvectorMembership
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.LeviEigenvectorMembership

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} (G : Grp k n)

theorem mem_left_iff (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet) (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet)
    {g : GL (Fin n) k} (hg : g ∈ G.JSet) (h : GL (Fin n) k) : g * h ∈ G.JSet ↔ h ∈ G.JSet := by
  refine ⟨fun hgh => ?_, fun hh => hmul g hg h hh⟩
  have := hmul _ (hinv g hg) _ hgh
  simpa [← mul_assoc] using this

theorem mem_right_iff (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet) (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet)
    {h : GL (Fin n) k} (hh : h ∈ G.JSet) (g : GL (Fin n) k) : g * h ∈ G.JSet ↔ g ∈ G.JSet := by
  refine ⟨fun hgh => ?_, fun hg => hmul g hg h hh⟩
  have := hmul _ hgh _ (hinv h hh)
  simpa [mul_assoc] using this

theorem levi_eigenvector_of_conditions (hcb : CompactConductorBasicProp (k := k)) (hccB : CompactConductorBoundProp G) (hΔU : ModulusOnUnitsProp G) (hΔM : ModulusMultiplicativeProp G)
    (hJone : JacquetOneProp G) (hJmul : JacquetMultiplicativeProp G) (hJinv : JacquetInverseProp G) (hlM : LambdaMultiplicativeProp G)
    (hlB : LambdaBasicProp G) (hKC : CompactOpenKernelProp G) :
    G.v0 ∈ G.V0sp ∧ G.v0 ≠ 0 ∧ ∀ j : ↥(KO k (Fin n)), (j : GL (Fin n) k) ∈ G.JSet →
      Rreg (k := k) (n := n) j G.v0 = G.lam j • G.v0 := by
  have hmul := hJmul hcb hccB
  have hinv := hJinv hcb hccB
  have hlam := hlM hcb hΔU hΔM hccB
  obtain ⟨hl1, -, hlK⟩ := hlB hccB
  have hKJ : KC k n G.lev ⊆ G.JSet := (hKC hccB G.lev).2.2.2.2 le_rfl

  have hright : ∀ (g j : ↥(KO k (Fin n))), (j : GL (Fin n) k) ∈ G.JSet →
      G.v0 (g * j) = G.lam j * G.v0 g := by
    intro g j hj
    simp only [Grp.v0, Subgroup.coe_mul, mem_right_iff G hmul hinv hj]
    split_ifs with hg
    · rw [hlam _ hg _ hj, mul_comm]
    · simp
  refine ⟨⟨fun p hp g => ?_, fun g u hu => ?_⟩, ?_, fun j hj => ?_⟩
  · have hpJ : (p : GL (Fin n) k) ∈ G.JSet := hJone.2 hp
    simp only [Grp.v0, Subgroup.coe_mul, mem_left_iff G hmul hinv hpJ]
    split_ifs with hg
    · rw [hlam _ hpJ _ hg]
    · simp
  · rw [hright g u (hKJ hu), hlK _ hu, one_mul]
  · intro h0
    have := congrFun h0 1
    simp only [Grp.v0, OneMemClass.coe_one, if_pos hJone.1, hl1, Pi.zero_apply] at this
    exact one_ne_zero this
  · funext g
    rw [Pi.smul_apply, smul_eq_mul, ← hright g j hj]
    rfl

end UpperTheory.TNZ.Grp.LeviEigenvectorMembership

namespace UpperTheory.TNZ.Grp

theorem leviEigenvector_holds {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : NonzeroLeviEigenvectorExists G :=
  fun hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC =>
    LeviEigenvectorMembership.levi_eigenvector_of_conditions G hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PArtinIne
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

namespace P_artinIne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ}

theorem val_ine (ha : IsLocalArtin h a) (t : Ine (F := E) A) :
    valuation (w.adicCompletion E) ((a (ineIncl h t) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
  have h0 := ha.ord_eq (ineIncl h t)
  rw [deg_ineIncl, neg_zero] at h0
  exact ord_eq_zero_iff.mp h0

theorem exists_ine (ha : IsLocalArtin h a) (u : (w.adicCompletion E)ˣ)
    (hu : valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1) :
    ∃ t : Ine (F := E) A, a (ineIncl h t) = u := by
  obtain ⟨σ, hσ⟩ := ha.surj u
  have h0 := ha.ord_eq σ
  rw [hσ, ord_eq_zero hu] at h0
  have hd : deg σ = 0 := by omega
  refine ⟨⟨(σ : G E Ω), deg_eq_zero_iff.mp hd⟩, ?_⟩
  have e : ineIncl h ⟨(σ : G E Ω), deg_eq_zero_iff.mp hd⟩ = σ := Subtype.ext rfl
  rw [e, hσ]

end P_artinIne

theorem step_artinIne : ArtinInertiaProp := by
  intro E Ω _ _ _ _ _ A w h a ha
  exact ⟨P_artinIne.val_ine ha, P_artinIne.exists_ine ha⟩

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PDMul
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_DMul

theorem minor_mul_sub_mem {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (Q : Ideal R) (A B : Matrix ι ι R) (hB : ∀ i j, ¬ p i → p j → B i j ∈ Q) :
    ((A * B).submatrix (Subtype.val : {i // p i} → ι) Subtype.val).det -
      (A.submatrix (Subtype.val : {i // p i} → ι) Subtype.val).det *
        (B.submatrix (Subtype.val : {i // p i} → ι) Subtype.val).det ∈ Q := by
  rw [← Ideal.Quotient.eq, RingHom.map_mul, RingHom.map_det, RingHom.map_det, RingHom.map_det, ← det_mul]
  congr 1
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Matrix.mul_apply, map_sum, map_mul]
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  have h0 : ∑ l : {x // ¬ p x}, (Ideal.Quotient.mk Q) (A i l) * (Ideal.Quotient.mk Q) (B l j) = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hB l j l.2 j.2), mul_zero]
  rw [h0, add_zero]

theorem minor_isUnit {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (M : Matrix ι ι R) (hM : IsUnit M.det) (hl : ∀ i j, ¬ p i → p j → M i j ∈ IsLocalRing.maximalIdeal R) :
    IsUnit (M.submatrix (Subtype.val : {i // p i} → ι) Subtype.val).det := by
  have ht := twoBlockTriangular_det ((IsLocalRing.residue R).mapMatrix M) p
    (fun i hi j hj => (IsLocalRing.residue_eq_zero_iff _).mpr (hl i j hi hj))
  rw [← RingHom.map_det] at ht
  have hu : IsUnit ((IsLocalRing.residue R) M.det) := hM.map _
  rw [ht] at hu
  have h1 := isUnit_of_mul_isUnit_left hu
  refine IsUnit.of_map (IsLocalRing.residue R) _ ?_
  rw [RingHom.map_det]
  exact h1

theorem unit_factor {R : Type} [CommRing R] [IsLocalRing R] (Q : Ideal R) (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (x y z : R) (hy : IsUnit y) (hz : IsUnit z) (hxyz : x - y * z ∈ Q) :
    ∃ u : Rˣ, (u : R) - 1 ∈ Q ∧ x = y * z * u := by
  obtain ⟨W, hW⟩ : IsUnit (y * z) := hy.mul hz
  have hsub : x * ((W⁻¹ : Rˣ) : R) - 1 ∈ Q := by
    have e : x * ((W⁻¹ : Rˣ) : R) - 1 = (x - y * z) * ((W⁻¹ : Rˣ) : R) := by
      rw [sub_mul, ← hW, Units.mul_inv]
    rw [e]
    exact Ideal.mul_mem_right _ _ hxyz
  have hunit : IsUnit (x * ((W⁻¹ : Rˣ) : R)) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hm
    have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hm (hQ hsub)
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec]; exact hsub
  · rw [IsUnit.unit_spec, ← hW, mul_left_comm, Units.mul_inv, mul_one]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem low {n : ℕ} (G : Grp k n) (a : Fin G.s) (h1 : (a : ℕ) + 1 < G.s) (X : GL (Fin n) 𝒪[k])
    (x : GL (Fin n) k) (hX : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) X = x) (hx : x ∈ G.JSet)
    (i j : Fin n) (hi : ¬ (G.bl i ≤ a)) (hj : G.bl j ≤ a) :
    (X : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ cc G.μ a ⟨a + 1, h1⟩ := by
  have hlt : G.bl j < G.bl i := lt_of_le_of_lt hj (not_le.mp hi)
  obtain ⟨y, hy, hyx⟩ := hx.2 i j hlt
  have hyX : y = (X : Matrix (Fin n) (Fin n) 𝒪[k]) i j := by
    apply FaithfulSMul.algebraMap_injective 𝒪[k] k
    rw [hyx, ← hX]
    rfl
  rw [← hyX]
  have hia : (a : ℕ) < (G.bl i : ℕ) := not_le.mp hi
  have hle : cc G.μ a ⟨a + 1, h1⟩ ≤ cc G.μ (G.bl j) (G.bl i) :=
    G.ball (G.bl j) a ⟨a + 1, h1⟩ (G.bl i) hj (Fin.lt_def.mpr (Nat.lt_succ_self _)) (Fin.le_def.mpr hia)
  exact Ideal.pow_le_pow_right hle hy

theorem delta_eq {n : ℕ} (G : Grp k n) (a : Fin G.s) (X : Matrix (Fin n) (Fin n) 𝒪[k]) (x : GL (Fin n) k)
    (hx : (x : Matrix (Fin n) (Fin n) k) = X.map (algebraMap 𝒪[k] k)) :
    G.Δ a x = algebraMap 𝒪[k] k (X.submatrix (Subtype.val : {i : Fin n // G.bl i ≤ a} → Fin n) Subtype.val).det := by
  unfold Grp.Δ
  rw [hx, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem coe_map_eq {n : ℕ} (X : GL (Fin n) 𝒪[k]) (x : GL (Fin n) k)
    (hX : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) X = x) :
    (x : Matrix (Fin n) (Fin n) k) = (X : Matrix (Fin n) (Fin n) 𝒪[k]).map (algebraMap 𝒪[k] k) := by
  rw [← hX]; rfl

end UpperTheory.TNZ.Grp.P_DMul

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_DMul {n : ℕ} (G : Grp k n) : ModulusMultiplicativeProp G := by
  intro _ hB g hg h hh a h1
  have hab : a ≠ ⟨a + 1, h1⟩ := fun e => by
    have := congrArg Fin.val e
    simp at this
  have hc1 : 1 ≤ cc G.μ a ⟨a + 1, h1⟩ := hB.1 a _ hab
  have hQ : IsLocalRing.maximalIdeal 𝒪[k] ^ cc G.μ a ⟨a + 1, h1⟩ ≤ IsLocalRing.maximalIdeal 𝒪[k] := by
    have := Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal 𝒪[k]) hc1
    rwa [pow_one] at this
  obtain ⟨G', hG'⟩ := hg.1
  obtain ⟨H', hH'⟩ := hh.1
  have uG := P_DMul.minor_isUnit (fun i => G.bl i ≤ a) _ ((Matrix.isUnit_iff_isUnit_det _).mp G'.isUnit)
    (fun i j hi hj => hQ (P_DMul.low G a h1 G' g hG' hg i j hi hj))
  have uH := P_DMul.minor_isUnit (fun i => G.bl i ≤ a) _ ((Matrix.isUnit_iff_isUnit_det _).mp H'.isUnit)
    (fun i j hi hj => hQ (P_DMul.low G a h1 H' h hH' hh i j hi hj))
  have key := P_DMul.minor_mul_sub_mem (fun i => G.bl i ≤ a) _ (G' : Matrix (Fin n) (Fin n) 𝒪[k]) _
    (P_DMul.low G a h1 H' h hH' hh)
  obtain ⟨u, hu1, hu2⟩ := P_DMul.unit_factor _ hQ _ _ _ uG uH key
  refine ⟨u, hu1, ?_⟩
  have hgm := P_DMul.coe_map_eq G' g hG'
  have hhm := P_DMul.coe_map_eq H' h hH'
  have hghm : ((g * h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      ((G' : Matrix (Fin n) (Fin n) 𝒪[k]) * (H' : Matrix (Fin n) (Fin n) 𝒪[k])).map (algebraMap 𝒪[k] k) := by
    rw [Units.val_mul, hgm, hhm, Matrix.map_mul]
  rw [P_DMul.delta_eq G a _ _ hghm, P_DMul.delta_eq G a _ _ hgm, P_DMul.delta_eq G a _ _ hhm, ← map_mul, ← map_mul]
  exact congrArg _ hu2

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PDUnit
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

namespace P_DUnit

theorem isUnit_det_sub (A : GL (Fin n) 𝒪[k]) (a : Fin G.s)
    (hA : ∀ i j, G.bl j < G.bl i → (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k]) :
    IsUnit ((A : Matrix (Fin n) (Fin n) 𝒪[k]).submatrix
      (Subtype.val : {i : Fin n // G.bl i ≤ a} → Fin n) Subtype.val).det := by
  set M := (IsLocalRing.residue 𝒪[k]).mapMatrix (A : Matrix (Fin n) (Fin n) 𝒪[k]) with hM
  have hdet : IsUnit M.det := by
    rw [hM, ← RingHom.map_det]
    exact (Matrix.isUnits_det_units A).map _
  have htri := Matrix.twoBlockTriangular_det M (fun i => G.bl i ≤ a) (fun i hi j hj => by
    rw [hM, RingHom.mapMatrix_apply, Matrix.map_apply, IsLocalRing.residue_eq_zero_iff]
    exact hA i j (lt_of_le_of_lt hj (not_le.1 hi)))
  rw [htri] at hdet
  have h1 := isUnit_of_mul_isUnit_left hdet
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  exact h1.ne_zero

end P_DUnit

theorem step_DUnit : ModulusOnUnitsProp G := by
  intro hb g hg a
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.1 hg.1
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  have hA : ∀ i j, G.bl j < G.bl i →
      (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro i j hij
    obtain ⟨y, hy, hyx⟩ := hg.2 i j hij
    have hc : cc G.μ (G.bl j) (G.bl i) ≠ 0 := by
      have := hb.1 (G.bl j) (G.bl i) (ne_of_lt hij)
      omega
    have : y = (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j := hinj (by rw [hyx]; rfl)
    rw [← this]
    exact Ideal.pow_le_self hc hy
  have hu := P_DUnit.isUnit_det_sub G A a hA
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, RingHom.map_det]
  rfl

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PJinv
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} (G : Grp k n)

namespace P_Jinv

def CcUm : Prop :=
  ∀ a b c : Fin G.s, cc G.μ a a = 0 ∧ cc G.μ a b = cc G.μ b a ∧ cc G.μ a c ≤ max (cc G.μ a b) (cc G.μ b c)

def fe (i j : Fin n) : ℕ := if G.bl j < G.bl i then cc G.μ (G.bl j) (G.bl i) else 0

theorem fe_self (i : Fin n) : fe G i i = 0 := by simp [fe]

theorem fe_tri (hU : CcUm G) (i l j : Fin n) : fe G i j ≤ fe G i l + fe G l j := by
  by_cases hij : G.bl j < G.bl i
  · have e1 : fe G i j = cc G.μ (G.bl j) (G.bl i) := if_pos hij
    rw [e1]
    rcases le_or_gt (G.bl l) (G.bl j) with hlj | hjl
    · have e2 : fe G i l = cc G.μ (G.bl l) (G.bl i) := if_pos (lt_of_le_of_lt hlj hij)
      rw [e2]
      exact le_add_right (G.ball _ _ _ _ hlj hij le_rfl)
    · rcases le_or_gt (G.bl i) (G.bl l) with hil | hli
      · have e3 : fe G l j = cc G.μ (G.bl j) (G.bl l) := if_pos hjl
        rw [e3]
        exact le_add_left (G.ball _ _ _ _ le_rfl hij hil)
      · have e2 : fe G i l = cc G.μ (G.bl l) (G.bl i) := if_pos hli
        have e3 : fe G l j = cc G.μ (G.bl j) (G.bl l) := if_pos hjl
        rw [e2, e3]
        have := (hU (G.bl j) (G.bl l) (G.bl i)).2.2
        omega
  · have e1 : fe G i j = 0 := if_neg hij
    omega

def S (hU : CcUm G) : Subalgebra 𝒪[k] (Matrix (Fin n) (Fin n) 𝒪[k]) where
  carrier := {A | ∀ i j, A i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ fe G i j}
  mul_mem' := by
    intro A B hA hB i j
    simp only [Set.mem_ofPred_eq] at hA hB
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun l _ => ?_
    refine Ideal.pow_le_pow_right (fe_tri G hU i l j) ?_
    rw [pow_add]
    exact Ideal.mul_mem_mul (hA i l) (hB l j)
  one_mem' := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs with h
    · subst h
      rw [fe_self, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · exact zero_mem _
  add_mem' := by
    intro A B hA hB i j
    simp only [Set.mem_ofPred_eq] at hA hB
    exact Ideal.add_mem _ (hA i j) (hB i j)
  zero_mem' := fun _ _ => zero_mem _
  algebraMap_mem' := by
    intro r i j
    rw [Matrix.algebraMap_matrix_apply]
    split_ifs with h
    · subst h
      rw [fe_self, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · exact zero_mem _

theorem inv_mem (hU : CcUm G) (h : GL (Fin n) 𝒪[k])
    (hh : (h : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ S G hU) :
    ((h⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ S G hU := by
  set A : Matrix (Fin n) (Fin n) 𝒪[k] := (h : Matrix (Fin n) (Fin n) 𝒪[k]) with hAdef
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp h.isUnit
  rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
  obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_right hdet
  have h0 := Matrix.aeval_self_charpoly A
  rw [← Polynomial.X_mul_divX_add A.charpoly, map_add (f := _), map_mul, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have h1 : A * Polynomial.aeval A A.charpoly.divX = -algebraMap 𝒪[k] _ (A.charpoly.coeff 0) :=
    eq_neg_of_add_eq_zero_left h0
  have key : A * (-((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) • Polynomial.aeval A A.charpoly.divX) = 1 := by
    rw [mul_smul_comm, h1, neg_smul_neg, ← hu, Algebra.smul_def, ← map_mul, Units.inv_mul, map_one]
  have hinv := Units.eq_inv_of_mul_eq_one_left key
  rw [← hinv]
  refine Subalgebra.smul_mem _ ?_ _
  have hval : Polynomial.aeval A A.charpoly.divX =
      (S G hU).val (Polynomial.aeval (⟨A, hh⟩ : S G hU) A.charpoly.divX) :=
    (Polynomial.aeval_algHom_apply (S G hU).val (⟨A, hh⟩ : S G hU) A.charpoly.divX)
  rw [hval]
  exact Subtype.prop _

end P_Jinv

open P_Jinv in
theorem step_Jinv : JacquetInverseProp G := by
  intro hU0 hB g hg
  have hU : CcUm G := hU0 G.s G.μ (fun a b => ⟨_, hB.2.2.2 a b⟩)
  obtain ⟨hK, hJ⟩ := hg
  obtain ⟨h, rfl⟩ := hK
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  have hmem : (h : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ S G hU := by
    intro a b
    by_cases hab : G.bl b < G.bl a
    · obtain ⟨y, hy, hyx⟩ := hJ a b hab
      have hy' : y = (h : Matrix (Fin n) (Fin n) 𝒪[k]) a b := hinj hyx
      have e1 : fe G a b = cc G.μ (G.bl b) (G.bl a) := if_pos hab
      rw [e1, ← hy']
      exact hy
    · have e1 : fe G a b = 0 := if_neg hab
      rw [e1, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  have hi := inv_mem G hU h hmem
  refine ⟨⟨h⁻¹, (map_inv _ h)⟩, fun i j hij => ?_⟩
  refine ⟨((h⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) i j, ?_, ?_⟩
  · have := hi i j
    have e1 : fe G i j = cc G.μ (G.bl j) (G.bl i) := if_pos hij
    rwa [e1] at this
  · rw [← map_inv]
    rfl

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PJone
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace P_Jone

theorem inPow_zero (c : ℕ) : InPow c (0 : k) :=
  ⟨0, zero_mem _, map_zero _⟩

end P_Jone

theorem step_Jone {n : ℕ} (G : Grp k n) : G.JacquetOneProp := by
  refine ⟨⟨Subgroup.one_mem _, fun i j hij => ?_⟩, fun g hg => ⟨hg.1, fun i j hij => ?_⟩⟩
  · have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    rw [Units.val_one, Matrix.one_apply_ne hne]
    exact P_Jone.inPow_zero _
  · rw [(mem_parab.1 hg.2) i j hij]
    exact P_Jone.inPow_zero _

end Grp

end UpperTheory.TNZ
end
end

