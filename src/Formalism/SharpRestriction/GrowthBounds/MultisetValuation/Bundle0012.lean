module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0010
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0011

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EnInParamKProd
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section LogInv

variable (p : ℕ) [Fact p.Prime] (K1 : Type) [Field K1] [Algebra (K0 p) K1]

def en_L : PowerSeries K1 := PowerSeries.map (algebraMap (K0 p) K1) (logF p)

theorem en_logF_zero : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, logF, PowerSeries.coeff_mk]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  simp [hp.ne']

theorem en_logF_one : PowerSeries.coeff 1 (logF p) = 1 := by
  rw [logF, PowerSeries.coeff_mk]
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h1 : (1 : ℕ) ≠ p ^ (2 * 1) := by
    have : 1 < p ^ (2 * 1) := Nat.one_lt_pow (by norm_num) hp
    omega
  rw [if_neg h1]
  simp

theorem en_L_zero : PowerSeries.constantCoeff (en_L p K1) = 0 := by
  rw [en_L, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, en_logF_zero, map_zero]

theorem en_L_one : IsUnit (PowerSeries.coeff 1 (en_L p K1)) := by
  rw [en_L, PowerSeries.coeff_map, en_logF_one, map_one]
  exact isUnit_one

def en_E : PowerSeries K1 := (en_L p K1).substInvOfIsUnit (en_L_one p K1)

theorem en_E_zero : PowerSeries.constantCoeff (en_E p K1) = 0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit _ _

variable {ι : Type}

def en_aL (i : ι) : MvPowerSeries ι K1 := PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1) (en_L p K1)

def en_Ec (i : ι) : MvPowerSeries ι K1 := PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1) (en_E p K1)

theorem en_inParamK_eq (f : MvPowerSeries ι K1) : inParamK p K1 f = MvPowerSeries.subst (en_aL p K1) f := rfl

theorem en_aL_zero (i : ι) : MvPowerSeries.constantCoeff (en_aL p K1 i) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (en_L_zero p K1)

theorem en_Ec_zero (i : ι) : MvPowerSeries.constantCoeff (en_Ec p K1 i) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (en_E_zero p K1)

variable [Finite ι]

theorem en_aL_hs : MvPowerSeries.HasSubst (en_aL p K1 : ι → MvPowerSeries ι K1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (en_aL_zero p K1)

theorem en_Ec_hs : MvPowerSeries.HasSubst (en_Ec p K1 : ι → MvPowerSeries ι K1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (en_Ec_zero p K1)

theorem en_aL_Ec (i : ι) : MvPowerSeries.subst (en_aL p K1) (en_Ec p K1 i) = (MvPowerSeries.X i : MvPowerSeries ι K1) := by
  have h1 : MvPowerSeries.subst (en_aL p K1) (en_Ec p K1 i) =
      PowerSeries.subst (en_aL p K1 i) (en_E p K1) := by
    unfold en_Ec PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X i).const (en_aL_hs p K1)]
    simp only [MvPowerSeries.subst_X (en_aL_hs p K1)]
  rw [h1, en_aL, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (en_L_zero p K1)) (PowerSeries.HasSubst.X i), en_E,
    PowerSeries.subst_substInvOfIsUnit_left _ (en_L_zero p K1), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]

theorem en_Ec_aL (i : ι) : MvPowerSeries.subst (en_Ec p K1) (en_aL p K1 i) = (MvPowerSeries.X i : MvPowerSeries ι K1) := by
  have h1 : MvPowerSeries.subst (en_Ec p K1) (en_aL p K1 i) =
      PowerSeries.subst (en_Ec p K1 i) (en_L p K1) := by
    unfold en_aL PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X i).const (en_Ec_hs p K1)]
    simp only [MvPowerSeries.subst_X (en_Ec_hs p K1)]
  rw [h1, en_Ec, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (en_E_zero p K1)) (PowerSeries.HasSubst.X i), en_E,
    PowerSeries.subst_substInvOfIsUnit_right _ (en_L_zero p K1), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]

theorem en_Ec_inParamK (U : MvPowerSeries ι K1) : MvPowerSeries.subst (en_Ec p K1) (inParamK p K1 U) = U := by
  rw [en_inParamK_eq, MvPowerSeries.subst_comp_subst_apply (en_aL_hs p K1) (en_Ec_hs p K1)]
  simp only [en_Ec_aL]
  rw [MvPowerSeries.subst_self]
  rfl

theorem en_inParamK_Ec (i : ι) : inParamK p K1 (en_Ec p K1 i) = (MvPowerSeries.X i : MvPowerSeries ι K1) :=
  en_aL_Ec p K1 i

theorem en_inParamK_mul (f g : MvPowerSeries ι K1) : inParamK p K1 (f * g) = inParamK p K1 f * inParamK p K1 g :=
  MvPowerSeries.subst_mul (en_aL_hs p K1) f g

theorem en_inParamK_prod {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K1) :
    inParamK p K1 (∏ i ∈ s, f i) = ∏ i ∈ s, inParamK p K1 (f i) := by
  simp only [en_inParamK_eq, ← MvPowerSeries.coe_substAlgHom (en_aL_hs p K1), map_prod]

theorem en_inParamK_pow (f : MvPowerSeries ι K1) (n : ℕ) : inParamK p K1 (f ^ n) = inParamK p K1 f ^ n :=
  MvPowerSeries.subst_pow (en_aL_hs p K1) f n

theorem en_Ec_supp {Pl : Type} (π : ι → Pl) (i : ι) : en_Ec p K1 i ∈ Gen.SuppOn (R := K1) π (π i) := by
  unfold en_Ec PowerSeries.subst
  exact Gen.subst_mem (π := fun _ : Unit => π i) (PowerSeries.HasSubst.X i).const (fun _ _ _ _ => rfl)
    (fun _ _ => Gen.X_mem rfl)

end LogInv

theorem en_expS_supp {p : ℕ} [Fact p.Prime] {ι Pl : Type} (π : ι → Pl) (v : Pl) {f : MvPowerSeries ι (K0 p)}
    (hf : f ∈ Gen.SuppOn π v) : expS p f ∈ Gen.SuppOn π v := by
  intro n hn
  have e : MvPowerSeries.coeff n (expS p f) =
      ∑ k ∈ range (n.degree + 1), ((k.factorial : K0 p))⁻¹ * MvPowerSeries.coeff n (f ^ k) := rfl
  rw [e] at hn
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact (Subring.pow_mem _ hf k) n (right_ne_zero_of_mul hk)

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def en_pi (j : ℕ) : X.EA j ⊕ X.EA j → X.Pl := Sum.elim Sigma.fst Sigma.fst

theorem en_coordZA_zero (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    MvPowerSeries.constantCoeff (X.coordZA K' j x) = 0 := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]

theorem en_coordZA_hs (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) : MvPowerSeries.HasSubst (X.coordZA K' j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (en_coordZA_zero X K' j)

theorem en_coordZA_supp (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    X.coordZA K' j x ∈ Gen.SuppOn (R := K') (Sigma.fst : X.ZA j → X.Pl) (en_pi X j x) := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩
  · exact Subring.sum_mem _ fun s _ => Subring.mul_mem _ (Gen.C_mem _) (Gen.X_mem rfl)
  · exact Subring.sum_mem _ fun s _ => Subring.mul_mem _ (Gen.C_mem _) (Gen.X_mem rfl)

theorem en_ThZA_supp (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (v : X.Pl)
    {f : MvPowerSeries (X.EA j ⊕ X.EA j) K'} (hf : f ∈ Gen.SuppOn (en_pi X j) v) :
    X.ThZA K' j f ∈ Gen.SuppOn (Sigma.fst : X.ZA j → X.Pl) v :=
  Gen.subst_mem (en_coordZA_hs X K' j) hf fun s hs => hs ▸ en_coordZA_supp X K' j s

theorem en_ThZA_mul (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (f g : MvPowerSeries (X.EA j ⊕ X.EA j) K') :
    X.ThZA K' j (f * g) = X.ThZA K' j f * X.ThZA K' j g :=
  MvPowerSeries.subst_mul (en_coordZA_hs X K' j) f g

theorem en_ThZA_prod (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) {α : Type} (s : Finset α)
    (f : α → MvPowerSeries (X.EA j ⊕ X.EA j) K') : X.ThZA K' j (∏ i ∈ s, f i) = ∏ i ∈ s, X.ThZA K' j (f i) := by
  unfold Sys.ThZA
  simp only [← MvPowerSeries.coe_substAlgHom (en_coordZA_hs X K' j), map_prod]

theorem en_ThZA_pow (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (f : MvPowerSeries (X.EA j ⊕ X.EA j) K')
    (n : ℕ) : X.ThZA K' j (f ^ n) = X.ThZA K' j f ^ n :=
  MvPowerSeries.subst_pow (en_coordZA_hs X K' j) f n

def en_F (j : ℕ) (v : X.Pl) : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc :=
  MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v))

theorem en_PhAt_supp (j : ℕ) (v : X.Pl) : Y.PhAt j v ∈ Gen.SuppOn (en_pi X j) v := by
  unfold Pend.PhAt
  refine Subring.sum_mem _ fun e _ => ?_
  unfold sub2
  refine Gen.subst_mem (π := fun _ : Fin 2 => v) MvPowerSeries.HasSubst.X_X (fun _ _ _ _ => rfl) fun s _ => ?_
  fin_cases s
  · exact Gen.X_mem rfl
  · exact Gen.X_mem rfl

theorem en_F_supp (j : ℕ) (v : X.Pl) : en_F X Y j v ∈ Gen.SuppOn (en_pi X j) v :=
  Gen.map_mem _ (en_expS_supp _ v (Subring.neg_mem _ (en_PhAt_supp X Y j v)))

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HkLatTupUpdate
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

section Loc

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem between_fin (p k : ℕ) (hfin : Finite (W ⧸ Ideal.span {(p : W)})) (L : Submodule W (Fin k → Qq))
    (hL : IsLattice W L) :
    {A : Submodule W (Fin k → Qq) | A ≤ L ∧ ∀ x ∈ L, (p : W) • x ∈ A}.Finite := by
  classical
  obtain ⟨g, -, hg⟩ := hL
  have hfg : L.FG := by
    rw [hg]; exact Submodule.fg_span (Set.finite_range _)
  have : Module.Finite W L := Module.Finite.iff_fg.mpr hfg
  set I : Ideal W := Ideal.span {(p : W)} with hI
  have : Module.Finite (W ⧸ I) (↥L ⧸ I • (⊤ : Submodule W L)) :=
    Module.Finite.of_restrictScalars_finite W _ _
  have : Finite (↥L ⧸ I • (⊤ : Submodule W L)) := Module.finite_of_finite (W ⧸ I)
  let f : Submodule W (Fin k → Qq) → Set (↥L ⧸ I • (⊤ : Submodule W L)) :=
    fun A => ((A.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ : Set _)
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  have key : ∀ A : Submodule W (Fin k → Qq), (∀ x ∈ L, (p : W) • x ∈ A) →
      I • (⊤ : Submodule W L) ≤ A.comap L.subtype := by
    intro A hA
    rw [Submodule.smul_le]
    intro a ha x _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [mul_smul]
    apply Submodule.smul_mem
    show (p : W) • (x : Fin k → Qq) ∈ A
    exact hA x x.2
  intro A hA B hB hAB
  have h1 : (A.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ =
      (B.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ := SetLike.coe_injective hAB
  have h2 := congrArg (Submodule.comap (I • (⊤ : Submodule W L)).mkQ) h1
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_eq_right.mpr (key A hA.2),
    sup_eq_right.mpr (key B hB.2)] at h2
  have h3 := congrArg (Submodule.map L.subtype) h2
  rw [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.mpr hA.1,
    inf_eq_right.mpr hB.1] at h3
  exact h3

theorem up_fin_gen (p n' r k : ℕ) (hfin : Finite (W ⧸ Ideal.span {(p : W)})) (hp : algebraMap W Qq (p : W) ≠ 0)
    (A : Submodule W (Fin k → Qq)) :
    {A1 : Submodule W (Fin k → Qq) | IsEdge p n' r ⟨A, A1⟩}.Finite := by
  by_cases hA : IsLattice W A
  · let φ : (Fin k → Qq) →ₗ[W] (Fin k → Qq) := (p : W) • LinearMap.id
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 : (p : W) • x = (p : W) • y := hxy
      rw [← algebraMap_smul Qq (p : W) x, ← algebraMap_smul Qq (p : W) y] at h1
      exact smul_right_injective _ hp h1
    refine Set.Finite.of_finite_image (f := fun A1 => A1.map φ) ((between_fin p k hfin A hA).subset ?_)
      (fun a _ b _ h => Submodule.map_injective_of_injective hφ h)
    rintro _ ⟨A1, hA1, rfl⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hA1.2.2.2.1 x hx
    · intro x hx
      exact ⟨x, hA1.2.2.1 hx, rfl⟩
  · apply Set.Finite.subset Set.finite_empty
    intro A1 h
    exact (hA h.1).elim

theorem count_fun (hC : CountLoc) (p n' : ℕ) [IsDomain W] [IsDiscreteValuationRing W] (h1 : IsFractionRing W Qq)
    (h2 : Irreducible (p : W)) (h3 : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (N N' g i : ℕ) (hN : N' = N + g)
    (A : Submodule W (Fin N → Qq)) (B : Submodule W (Fin N' → Qq)) (hA : IsLattice W A) (hB : IsLattice W B)
    (SB : Finset (Submodule W (Fin N' → Qq))) (hSB : ∀ B1, B1 ∈ SB ↔ IsEdge p n' i ⟨B1, B⟩)
    (SA : ℕ → Finset (Submodule W (Fin N → Qq))) (hSA : ∀ k A1, A1 ∈ SA k ↔ IsEdge p n' k ⟨A, A1⟩)
    (x : Matrix (Fin N') (Fin N) Qq) :
    (∑ B1 ∈ SB, (by classical exact if ∀ y ∈ A, x.mulVec y ∈ B1 then (1 : ℚ) else 0)) =
      ∑ l ∈ range (i + 1), (((p ^ n') ^ ((i - l) * (g - l)) * Formalism.G0.gaussBinom (p ^ n') g l : ℕ) : ℚ) *
        ∑ A1 ∈ SA (i - l), (by classical exact if ∀ y ∈ A1, x.mulVec y ∈ B then (1 : ℚ) else 0) := by
  classical
  have e1 : ∀ (M : ℕ) (S : Finset (Submodule W (Fin M → Qq))) (E Pp : Submodule W (Fin M → Qq) → Prop)
      (_ : ∀ Z, Z ∈ S ↔ E Z), (∑ Z ∈ S, if Pp Z then (1 : ℚ) else 0) =
        (Nat.card {Z : Submodule W (Fin M → Qq) // E Z ∧ Pp Z} : ℚ) := by
    intro M S E Pp hS
    rw [Finset.sum_boole]
    congr 1
    rw [← Nat.card_eq_fintype_card.trans (Fintype.card_coe (S.filter Pp))]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun Z => by rw [Finset.mem_filter, hS]
  have := hC p n' W Qq h1 h2 h3 N N' g i hN A B hA hB x
  convert congrArg (fun n : ℕ => (n : ℚ)) this using 1
  · exact e1 N' SB _ _ hSB
  · push_cast
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    exact e1 N (SA (i - l)) _ _ (hSA (i - l))

end Loc

section PlacesLevel

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem hk_pQ_ne (v : Fin P.nV) : algebraMap (P.W v) (P.Qq v) (p : P.W v) ≠ 0 := by
  have := (P.setting v).frac_alt
  exact (map_ne_zero_iff _ (IsFractionRing.injective (P.W v) (P.Qq v))).2 (P.setting v).p_unif.ne_zero

theorem up_fin (v : Fin P.nV) (i : ℕ) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    {A1 : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨A, A1⟩}.Finite := by
  apply up_fin_gen
  · apply Nat.finite_of_card_ne_zero
    rw [(P.setting v).res_card]
    exact pow_ne_zero _ (P.setting v).prime.ne_zero
  · exact hk_pQ_ne P v

def UP (v : Fin P.nV) (i : ℕ) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    Finset (Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :=
  (up_fin P v i A).toFinset

theorem mem_UP {v : Fin P.nV} {i : ℕ} {A A1 : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} :
    A1 ∈ UP P v i A ↔ IsEdge p (P.n' v) i ⟨A, A1⟩ := by
  simp [UP]

theorem hk_latTup_update {L : P.Tup} (hL : P.IsLatTup L) (v : Fin P.nV)
    (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (hA : IsLattice (P.W v) A) :
    P.IsLatTup (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A) := by
  unfold Places.IsLatTup at *
  intro w
  by_cases h : w = v
  · subst h
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L w A w = A := by
      first
        | exact Function.update_self (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w A L
        | exact Function.update_same (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w A L
    exact (congrArg (fun Z => IsLattice (P.W w) Z) e).mpr hA
  · have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A w = L w := Function.update_of_ne (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) h A L
    exact (congrArg (fun Z => IsLattice (P.W w) Z) e).mpr (hL w)

theorem latTup_smul (C : Level P) (γ : C.Γ) (L : P.Tup) : P.IsLatTup (C.smul γ L) ↔ P.IsLatTup L := by
  constructor
  · intro h u
    have h1 : IsLattice (P.W u) ((L u).map (nt_phi (P.W u) (C.act u γ))) := h u
    have h2 := nt_lat_map (C.act u γ)⁻¹ _ h1
    rw [nt_map_inv] at h2
    exact h2
  · intro h u
    exact nt_lat_map (C.act u γ) (L u) (h u)

end PlacesLevel

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcTsumOdd
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem nc_notSg {T p : ℕ} (hg : GIdx D.host T p) : ¬ Formalism.MainNotions.G.IsSg D p := by
  intro h
  have h1 : D.host.cls p = PrimeClass.inertClass := hg.2.2.1
  unfold Formalism.MainNotions.G.IsSg at h
  rw [h1] at h
  exact absurd h (by decide)

theorem nc_step {T p : ℕ} (hg : GIdx D.host T p) : Formalism.MainNotions.G.stepP D p = Formalism.MainNotions.G.hP D p := by
  unfold Formalism.MainNotions.G.stepP; rw [if_neg (nc_notSg hg)]

theorem nc_bs_iter (X : Formalism.MainNotions.G.Inst D L) (h t : Formalism.MainNotions.G.HH D) (i : ℕ) : X.bs h (t + i • h) = X.bs h t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]

theorem nc_bs_rep (X : Formalism.MainNotions.G.Inst D L) (h t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Finset.univ.image (X.bs h)) :
    X.bs h t0 = t0 := by
  obtain ⟨t1, _, rfl⟩ := Finset.mem_image.1 ht0
  obtain ⟨i, hi⟩ := X.bs_orb h t1
  have := nc_bs_iter X h (X.bs h t1) i
  rw [hi] at this
  exact this.symm

theorem nc_partner {T p : ℕ} (hg : GIdx D.host T p) (t : Formalism.MainNotions.G.HH D) (e : ℕ) :
    Formalism.MainNotions.G.partner D p t e = (false, t + e • Formalism.MainNotions.G.hP D p) := by
  unfold Formalism.MainNotions.G.partner
  simp [nc_notSg hg]

theorem nc_tsum_odd (g : ℕ → ℝ) [DecidablePred (fun e : ℕ => Odd e)] :
    ∑' e : ℕ, (if Odd e then g e else 0) = ∑' e : ℕ, g (2 * e + 1) := by
  have hi : Function.Injective (fun e : ℕ => 2 * e + 1) := by
    intro a b h
    simp only at h
    omega
  have hs : Function.support (fun e : ℕ => if Odd e then g e else 0) ⊆ Set.range (fun e : ℕ => 2 * e + 1) := by
    intro e he
    by_cases ho : Odd e
    · obtain ⟨k, rfl⟩ := ho
      exact ⟨k, by ring⟩
    · exact (he (if_neg ho)).elim
  rw [← hi.tsum_eq hs]
  congr 1
  funext e
  exact if_pos (odd_two_mul_add_one e)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

