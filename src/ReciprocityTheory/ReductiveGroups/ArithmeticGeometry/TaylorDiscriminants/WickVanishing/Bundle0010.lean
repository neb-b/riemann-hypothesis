module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FoldrIterateEqTG
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.G2.Gen

open ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {S : Type} [CommRing S] {ι : Type}
  (D : ι → S → S) (κ : k →+* S)

def PolG [Fintype ι] (P : MvPolynomial ι k) (A : S) : S :=
  ∑ n ∈ P.support, κ (P.coeff n) * (Finset.univ : Finset ι).toList.foldr (fun l g => (D l)^[n l] g) A

theorem TG_replicate (n : ℕ) (l : ι) (A : S) : TG D (List.replicate n l) A = (D l)^[n] A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Function.iterate_succ_apply', ← ih]
    rfl

theorem foldr_iterate_eq_TG (Ls : List ι) (m : ι →₀ ℕ) (A : S) :
    Ls.foldr (fun l g => (D l)^[m l] g) A = TG D (word Ls m) A := by
  induction Ls with
  | nil => rfl
  | cons l Ls ih =>
    rw [List.foldr_cons, ih]
    have e : word (l :: Ls) m = List.replicate (m l) l ++ word Ls m := by simp [word]
    rw [e, TG_append, TG_replicate]

theorem e_PolG [Fintype ι] (e : S →+* k) (he : ∀ a, e (κ a) = a) (P : MvPolynomial ι k) (A : S) :
    e (PolG D κ P A) = (AddMonoidAlgebra.coeff P).sum
      (fun n a => a * e (TG D (word (Finset.univ : Finset ι).toList n) A)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PolG, map_sum, map_mul, he, foldr_iterate_eq_TG]
  rfl

theorem half_gen [Algebra ℚ k] [Fintype ι]
    (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
    (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)
    (e : S →+* k) (he : ∀ a, e (κ a) = a) (c : ι → ι → k) (q : S) (hc : ∀ l l', c l l' = c l' l)
    (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))
    (P : MvPolynomial ι k) (A : S) :
    e (PolG D κ P (A * q)) = algebraMap ℚ k (1 / 2) * e (PolG D κ (secondOrder k c P) A) := by
  classical
  set ψ : List ι → k := fun w => e (TG D w A) with hψ
  rw [e_PolG D κ e he, e_PolG D κ e he]
  have h2 : (AddMonoidAlgebra.coeff (secondOrder k c P)).sum
      (fun n a => a * e (TG D (word (Finset.univ : Finset ι).toList n) A)) = lamW ψ (secondOrder k c P) := rfl
  rw [h2, lamW_secondOrder, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun n _ => ?_
  rw [e_TG_mul_q D κ hadd hC hmul e c q hq0 hq1 hq2 he]
  have h3 := sum_splits_evalTwo_word c hc (Finset.univ : Finset ι).toList (Finset.nodup_toList _) n ψ
  have h4 : (algebraMap ℚ k (1 / 2)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℚ k) 2, ← map_mul]; norm_num
  calc (AddMonoidAlgebra.coeff P) n * ((splits (word (Finset.univ : Finset ι).toList n)).map
        (fun p => e (TG D p.1 A) * ev2 c p.2)).sum
      = (AddMonoidAlgebra.coeff P) n * ((algebraMap ℚ k (1 / 2) * 2) *
          ((splits (word (Finset.univ : Finset ι).toList n)).map (fun p => ψ p.1 * ev2 c p.2)).sum) := by
        rw [h4, one_mul]
    _ = algebraMap ℚ k (1 / 2) * ((AddMonoidAlgebra.coeff P) n * rW ψ c n) := by
        rw [mul_assoc (algebraMap ℚ k (1 / 2)), h3]
        simp only [rW]
        ring

theorem kill_gen [Algebra ℚ k] [Fintype ι]
    (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
    (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)
    (e : S →+* k) (he : ∀ a, e (κ a) = a) (c : ι → ι → k) (q : S) (hc : ∀ l l', c l l' = c l' l)
    (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))
    (P : MvPolynomial ι k) (hP : secondOrder k c P = 0) (G Y : S) :
    e (PolG D κ P (G * (1 + q * Y))) = e (PolG D κ P G) := by
  have hsplit : G * (1 + q * Y) = G + G * Y * q := by ring
  have hlin : ∀ A B, PolG D κ P (A + B) = PolG D κ P A + PolG D κ P B := by
    intro A B
    simp only [PolG, foldr_iterate_eq_TG]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [TG_add, mul_add]
    exact hadd
  rw [hsplit, hlin, map_add (f := _), half_gen D κ hadd hC hmul e he c q hc hq0 hq1 hq2 P (G * Y), hP]
  simp [PolG]

end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LemmaH
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

abbrev kapH (m : ℕ) {ι π : Type} [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k) (l l' : ι) : k :=
  if c l = c l' ∧ s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0

theorem kapW_eq_kapH (m : ℕ) {ι π : Type} [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k)
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) :
    kapW m s (fun l => (u l, 0)) (fun l => (0, φ l)) = kapH m c s u φ := by
  funext l l'
  show (if s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0) =
    (if c l = c l' ∧ s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0)
  by_cases hs : s l = true ∧ s l' = false
  · rw [if_pos hs]
    by_cases hc : c l = c l'
    · rw [if_pos ⟨hc, hs⟩]
    · rw [if_neg (fun h => hc h.1), hFU l l' (fun h => hc h.1), mul_zero]
  · rw [if_neg hs, if_neg (fun h => hs h.2)]

theorem rename_qsmul {ι τ : Type} (e : ι → τ) (q : ℚ) (X : MvPolynomial ι k) :
    MvPolynomial.rename e (q • X) = q • MvPolynomial.rename e X := by
  exact map_rat_smul (MvPolynomial.rename e) q X

theorem ordNabla_expand (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι π : Type}
    [Fintype ι] [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k)
    (hUF : OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (0, φ l)))
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) (Q : MvPolynomial ι k) (g : PS k 1 d) :
    ordNabla k B h m s (fun l => (u l, φ l)) Q (liftX k g) =
      ∑ n ∈ Finset.range (Q.totalDegree + 1),
        nablaPoly k B h m u (((n.factorial : ℚ)⁻¹) • (secondOrder k (kapH m c s u φ))^[n] Q) (liftX k g) := by
  classical
  have hb0 : ∀ l, ((fun l => ((0 : Fin d → k), φ l)) l).1 = 0 := fun l => rfl
  have haa : ∀ l l', s l = s l' → betaH k (u l, (0 : Fin d → k)) (u l', 0) = 0 := by
    intro l l' _
    simp [betaH]
  have hab : ∀ l l', s l = s l' → betaH k (u l, (0 : Fin d → k)) (0, φ l') = 0 :=
    fun l l' hs => hUF l l' (fun h => h.2 hs)
  have ordNabla_wick (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type}
      [Fintype ι] (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (hb0 : ∀ l, (ξb l).1 = 0)
      (haa : ∀ l l', s l = s l' → betaH k (ξa l) (ξa l') = 0)
      (hab : ∀ l l', s l = s l' → betaH k (ξa l) (ξb l') = 0) (P : MvPolynomial ι k) (f : PS k 1 d) :
      ordNabla k B h m s (fun l => ξa l + ξb l) P (liftX k f) =
        ∑ n ∈ Finset.range ((MvPolynomial.rename (sideE s) P).totalDegree + 1),
          PI.WickFormula.ordEval (opL B h m s ξa) (opR B h m s ξa)
            (((n.factorial : ℚ)⁻¹) • MvPolynomial.rename (sideE s) ((secondOrder k (kapW m s ξa ξb))^[n] P))
            (liftX k f) := by
    have hbb : ∀ l l', betaH k (ξb l) (ξb l') = 0 := fun l l' => by
      rw [show ξb l = (0, (ξb l).2) from Prod.ext (hb0 l) rfl, show ξb l' = (0, (ξb l').2) from Prod.ext (hb0 l') rfl]
      exact betaH_zero_zero _ _
    have hba : ∀ l l', s l = s l' → betaH k (ξb l) (ξa l') = 0 := fun l l' e => by
      rw [betaH_antisymm, hab l' l e.symm, neg_zero]
    have cA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
      fun l l' e => nablaL_comm hN2 B h m _ _ (haa l l' e)
    have cAB : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
      fun l l' e => nablaL_comm hN2 B h m _ _ (hab l l' e)
    have cBA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
      fun l l' e => nablaL_comm hN2 B h m _ _ (hba l l' e)
    have cB : ∀ l l', Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
      fun l l' => nablaL_comm hN2 B h m _ _ (hbb l l')
    have hsum : ∀ l, nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2 =
        nablaL B h m (ξa l).1 (ξa l).2 + nablaL B h m (ξb l).1 (ξb l).2 := fun l =>
      nablaL_add B h m _ _ _ _
    have cAll : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2)
        (nablaL B h m (ξa l' + ξb l').1 (ξa l' + ξb l').2) := fun l l' e => by
      rw [hsum, hsum]
      exact ((cA l l' e).add_right (cAB l l' e)).add_left ((cBA l l' e).add_right (cB l l'))
    rw [ordNabla_eq B h m s (fun l => ξa l + ξb l) cAll P (liftX k f)]
    have hL : opL B h m s (fun l => ξa l + ξb l) = opL B h m s ξa + opL B h m s ξb := funext fun i => hsum _
    have hR : opR B h m s (fun l => ξa l + ξb l) = opR B h m s ξa + opR B h m s ξb := funext fun j => hsum _
    have key := _root_.wick_formula k (Module.End k (AA k d)) (AA k d) _ _ (opL B h m s ξa) (opL B h m s ξb)
      (opR B h m s ξa) (opR B h m s ξb) (kapE s (kapW m s ξa ξb)) (liftX k f)
      (fun i i' => ⟨cA _ _ (by rw [side_inl s i, side_inl s i']), cAB _ _ (by rw [side_inl s i, side_inl s i']),
        cB _ _⟩)
      (fun j j' => ⟨cA _ _ (by rw [side_inr s j, side_inr s j']), cAB _ _ (by rw [side_inr s j, side_inr s j']),
        cB _ _⟩)
      (fun i j => cB _ _)
      (fun i j => by
        rw [nablaL_bracket hN2 B h m]
        unfold kapE kapW
        rw [if_pos ⟨side_inl s i, side_inr s j⟩])
      (fun i => by
        rw [Module.End.smul_def, opL, hb0]
        exact hN3 R d O k B h m _ f)
      (fun j => by
        rw [Module.End.smul_def, opR, hb0]
        exact hN3 R d O k B h m _ f)
      (MvPolynomial.rename (sideE s) P)
    rw [hL, hR, ← Module.End.smul_def, key]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Module.End.smul_def, delta_pow_rename s _ (kapW_supp m s ξa ξb)]
  have ordNabla_u (hN2 : ConnectionCommutator) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type} [Fintype ι] (s : ι → Bool)
      (u : ι → Fin d → k) (P : MvPolynomial ι k) (G : AA k d) :
      ordNabla k B h m s (fun l => (u l, 0)) P G = nablaPoly k B h m u P G := by
    have hcomm : ∀ a b : ι, Function.Commute (nabla k B h m (u a) 0) (nabla k B h m (u b) 0) := by
      intro a b z
      have hz := hN2 R d O k B h m (u a, 0) (u b, 0) z
      have hb : betaH k (u a, (0 : Fin d → k)) (u b, 0) = 0 := by simp [betaH]
      rw [hb, mul_zero, map_zero, zero_mul] at hz
      exact sub_eq_zero.mp hz
    unfold ordNabla nablaPoly
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    rw [← List.foldr_append]
    refine List.Perm.foldr_eq' (List.filter_append_perm _ _) ?_ _
    intro x _ y _ z
    exact (hcomm y x).iterate_iterate (n y) (n x) z
  have hw := ordNabla_wick hN2 hN3 B h m s (fun l => (u l, 0)) (fun l => (0, φ l)) hb0 haa hab Q g
  simp only [Prod.mk_add_mk, add_zero, zero_add] at hw
  have hdeg : (MvPolynomial.rename (sideE s) Q).totalDegree = Q.totalDegree :=
    MvPolynomial.totalDegree_renameEquiv (R := k) (sideE s) Q
  rw [hw, kapW_eq_kapH m c s u φ hFU, hdeg]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← rename_qsmul, ← ordNabla_eq B h m s (fun l => (u l, 0)) ?_, ordNabla_u hN2]
  intro l l' _
  exact nablaL_comm hN2 B h m _ _ (by simp [betaH])

theorem ordNabla_value_expand (hV : ValueSt) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d)
    (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) {ι π : Type} [Fintype ι] [DecidableEq π] (c : ι → π)
    (s : ι → Bool) (u φ : ι → Fin d → k) (hUF : OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (0, φ l)))
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) (Q : MvPolynomial ι k) (g : PS k 1 d) :
    constantCoeff (ordNabla k B h m s (fun l => (u l, φ l)) Q (liftX k g)) =
      ∑ n ∈ Finset.range (Q.totalDegree + 1),
        constantCoeff (DpolyOf (B.FK k) u (((n.factorial : ℚ)⁻¹) • (secondOrder k (kapH m c s u φ))^[n] Q) g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ordNabla_expand hN2 hN3 B h m c s u φ hUF hFU Q g, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact hV R d O k B h hax m ι u _ g

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LiftXEqRename
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem expS_zero' {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  unfold FB.expS
  rw [PowerSeries.subst_zero_eq_C_constantCoeff]
  simp

theorem cc_expS {n : ℕ} (F : PS k n d) (hF : constantCoeff F = 0) : constantCoeff (FB.expS k F) = 1 := by
  have ha : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  have h1 : PowerSeries.exp k = 1 + (PowerSeries.exp k - 1) := by ring
  have h2 : PowerSeries.constantCoeff (PowerSeries.exp k - 1) = 0 := by simp
  unfold FB.expS
  rw [h1, ← PowerSeries.coe_substAlgHom ha, map_add (f := _), map_one, map_add (f := _), PowerSeries.coe_substAlgHom ha,
    PowerSeries.constantCoeff_subst_eq_zero hF _ h2, map_one, add_zero]

def embX (d : ℕ) : Fin 1 × Fin d ↪ Fin d ⊕ Fin d :=
  ⟨fun p => Sum.inl p.2, fun p q hpq => by
    obtain ⟨a, i⟩ := p
    obtain ⟨b, j⟩ := q
    simp only [Sum.inl.injEq] at hpq
    rw [Subsingleton.elim a b, hpq]⟩

theorem liftX_eq_rename (f : PS k 1 d) : liftX k f = rename (embX d) f := by
  rw [MvPowerSeries.rename_eq_subst]
  rfl

theorem cc_liftX (f : PS k 1 d) : constantCoeff (liftX k f) = constantCoeff f := by
  rw [liftX_eq_rename, MvPowerSeries.constantCoeff_rename]

theorem intAA_liftX (f : PS k 1 d) (hf : IntAA (R := R) k f) : IntAA (R := R) k (liftX k f) := by
  rw [liftX_eq_rename]
  intro n
  rw [MvPowerSeries.coeff_rename]
  exact Subring.sum_mem _ fun u _ => hf u

def GoodE (R : Type) [CommRing R] [Algebra R k] (E0 X : AA k d) : Prop :=
  ∃ G : AA k d, IntAA (R := R) k G ∧ X = E0 * G

theorem good_pow (E0 : AA k d) (T : Module.End k (AA k d)) (hT : ∀ X, GoodE R E0 X → GoodE R E0 (T X))
    (n : ℕ) : ∀ X, GoodE R E0 X → GoodE R E0 ((T ^ n) X) := by
  induction n with
  | zero =>
    intro X hX
    rw [pow_zero]
    exact hX
  | succ n ih =>
    intro X hX
    rw [pow_succ]
    exact ih (T X) (hT X hX)

theorem good_prod (E0 : AA k d) (L : List (Module.End k (AA k d)))
    (hL : ∀ T ∈ L, ∀ X, GoodE R E0 X → GoodE R E0 (T X)) : ∀ X, GoodE R E0 X → GoodE R E0 (L.prod X) := by
  induction L with
  | nil =>
    intro X hX
    rw [List.prod_nil]
    exact hX
  | cons T L ih =>
    intro X hX
    rw [List.prod_cons]
    exact hL T (by simp) _ (ih (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) X hX)

theorem good_ofFn (E0 : AA k d) {r : ℕ} (a : Fin r → Module.End k (AA k d))
    (ha : ∀ i X, GoodE R E0 X → GoodE R E0 (a i X)) (e : Fin r → ℕ) :
    ∀ X, GoodE R E0 X → GoodE R E0 ((List.ofFn fun i => a i ^ e i).prod X) := by
  refine good_prod E0 _ ?_
  intro T hT
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT
  exact good_pow E0 (a i) (ha i) (e i)

theorem cc_ordEval_mem (J : Submodule R k) (e : ℕ) (E0 : AA k d) (hE0 : constantCoeff E0 = 1) {r q : ℕ}
    (a : Fin r → Module.End k (AA k d)) (a' : Fin q → Module.End k (AA k d))
    (ha : ∀ i X, GoodE R E0 X → GoodE R E0 (a i X)) (ha' : ∀ j X, GoodE R E0 X → GoodE R E0 (a' j X))
    (σ : AA k d) (hσ : GoodE R E0 σ) (Q : MvPolynomial (Fin r ⊕ Fin q) k) (hQ : ∀ mo, Q.coeff mo ∈ J ^ e) :
    constantCoeff (PI.WickFormula.ordEval a a' Q σ) ∈ J ^ e := by
  unfold PI.WickFormula.ordEval
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, map_sum]
  refine Submodule.sum_mem _ fun mo _ => ?_
  have hgood : GoodE R E0 (((List.ofFn fun i => a i ^ mo (Sum.inl i)).prod *
      (List.ofFn fun j => a' j ^ mo (Sum.inr j)).prod) σ) :=
    good_ofFn E0 a ha _ _ (good_ofFn E0 a' ha' _ σ hσ)
  obtain ⟨G, hGi, hGe⟩ := hgood
  rw [LinearMap.smul_apply, hGe, MvPowerSeries.smul_eq_C_mul, map_mul, map_mul,
    MvPowerSeries.constantCoeff_C, hE0, one_mul]
  obtain ⟨r, hr⟩ := hGi 0
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← hr, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ r (hQ mo)

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogPoinc
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [Fintype τ] [DecidableEq τ]

def prim (ω : τ → MvPowerSeries τ k) : MvPowerSeries τ k := fun m =>
  algebraMap ℚ k ((m.degree : ℚ)⁻¹) *
    ∑ w, if m w = 0 then 0 else coeff (m - Finsupp.single w 1) (ω w)

theorem coeff_prim (ω : τ → MvPowerSeries τ k) (m : τ →₀ ℕ) :
    coeff m (prim ω) = algebraMap ℚ k ((m.degree : ℚ)⁻¹) *
      ∑ w, if m w = 0 then 0 else coeff (m - Finsupp.single w 1) (ω w) := rfl

theorem constantCoeff_prim (ω : τ → MvPowerSeries τ k) : constantCoeff (prim ω) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_prim]
  simp

theorem degree_eq_sum (n : τ →₀ ℕ) : n.degree = ∑ w, n w := by
  classical
  unfold Finsupp.degree
  exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)

theorem pderiv_prim (ω : τ → MvPowerSeries τ k)
    (hω : ∀ a c, pderiv (R := k) c (ω a) = pderiv (R := k) a (ω c)) (v : τ) : pderiv (R := k) v (prim ω) = ω v := by
  ext m
  rw [coeff_pderiv, coeff_prim]
  set n := m + Finsupp.single v 1 with hn
  have key : ∀ w, (if n w = 0 then 0 else coeff (n - Finsupp.single w 1) (ω w)) * ((m v : k) + 1)
      = (n w : k) * coeff m (ω v) := by
    intro w
    by_cases hw : w = v
    · subst hw
      have h1 : n w = m w + 1 := by simp [hn]
      have h2 : n - Finsupp.single w 1 = m := by rw [hn]; exact add_tsub_cancel_right _ _
      rw [if_neg (by omega), h2, h1]
      push_cast
      ring
    · have h1 : n w = m w := by simp [hn, Finsupp.single_apply, hw, Ne.symm hw]
      by_cases hm : m w = 0
      · rw [if_pos (by rw [h1, hm]), h1, hm]
        simp
      · rw [if_neg (by rw [h1]; exact hm), h1]
        have hle : Finsupp.single w 1 ≤ m := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hm)
        have hc := congrArg (coeff (m - Finsupp.single w 1)) (hω w v)
        rw [coeff_pderiv, coeff_pderiv] at hc
        have e1 : m - Finsupp.single w 1 + Finsupp.single v 1 = n - Finsupp.single w 1 := by
          rw [hn]; exact tsub_add_eq_add_tsub hle
        have e2 : m - Finsupp.single w 1 + Finsupp.single w 1 = m := tsub_add_cancel_of_le hle
        have e3 : (m - Finsupp.single w 1 : τ →₀ ℕ) v = m v := by
          simp [Finsupp.single_apply, hw, Ne.symm hw]
        have e4' : (m - Finsupp.single w 1 : τ →₀ ℕ) w + 1 = m w := by
          rw [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
        have e4 : ((m - Finsupp.single w 1 : τ →₀ ℕ) w : k) + 1 = (m w : k) := by
          rw [← e4', Nat.cast_add, Nat.cast_one]
        rw [e1, e2, e3, e4] at hc
        rw [hc]
        ring
  have hsum : (∑ w, if n w = 0 then 0 else coeff (n - Finsupp.single w 1) (ω w)) * ((m v : k) + 1)
      = (n.degree : k) * coeff m (ω v) := by
    rw [Finset.sum_mul, Finset.sum_congr rfl (fun w _ => key w), ← Finset.sum_mul, degree_eq_sum,
      Nat.cast_sum]
  have hnv : n v = m v + 1 := by simp [hn]
  have hD : (n.degree : ℚ) ≠ 0 := by
    have : n v ≤ n.degree := by
      rw [degree_eq_sum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    exact_mod_cast (show n.degree ≠ 0 by omega)
  rw [mul_assoc, hsum, ← mul_assoc, ← map_natCast (algebraMap ℚ k) n.degree, ← map_mul,
    inv_mul_cancel₀ hD, map_one, one_mul]

end ReciprocityTheory.ChartRestriction.G.TB.LogPf
end
end

