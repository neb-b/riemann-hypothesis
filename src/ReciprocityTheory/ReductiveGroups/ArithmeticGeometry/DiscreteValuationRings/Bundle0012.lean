module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

section Basic

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem vge_of_zero {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))}
    (h : ∀ j, s.f j = 0) (r : ℚ) : VGe D F v k α s r := by
  unfold VGe
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun j => ?_⟩
  rw [h j, Fin.sum_univ_zero]

end Basic

theorem n4 : ValuationBoundAtZero := by
  intro V _ _ _ ϖ hϖ D Q _ F _ _ v hv m _ R' β s hsupp hnu w hw q hq
  classical
  obtain ⟨x, hx, hsum⟩ := hw
  have hxq : ∀ α, ((q : ℚ) : WithTop ℚ) ≤ v (x α) := by
    intro α
    by_cases h : ∃ z, α = β + R' • z
    · obtain ⟨z, rfl⟩ := h
      have h1 := GC.valuation_ge_at_zero hϖ hv (hnu (β + R' • z)) (hx _)
      refine le_trans (WithTop.coe_le_coe.2 ?_) h1
      rw [zero_add]; exact hq z
    · push Not at h
      exact GC.valuation_ge_at_zero hϖ hv (vge_of_zero (v := v) (hsupp α h) q) (hx α)
  obtain ⟨S, hS⟩ := hsum q
  have h1 := hS S le_rfl
  have h2 : ((q : ℚ) : WithTop ℚ) ≤ v (∑ α ∈ S, x α) := AddValuation.map_le_sum v fun α _ => hxq α
  have h3 := AddValuation.map_le_add v h1 h2
  rwa [sub_add_cancel] at h3

section Q

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ}

theorem bOf_zero_left (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (b : D.toPre.X) : bOf D.toPre Q 0 b = 0 := by
  simp [bOf, QForm.Q_zero hϖ D hQ]

theorem bOf_nsmul_left (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (n : ℕ) (a b : D.toPre.X) :
    bOf D.toPre Q (n • a) b = n * bOf D.toPre Q a b := by
  induction n with
  | zero => simp [bOf_zero_left hϖ hQ]
  | succ n ih => rw [succ_nsmul, QForm.bOf_add_left hϖ D hQ, ih]; push_cast; ring

theorem Q_nsmul (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (n : ℕ) (a : D.toPre.X) : Q (n • a) = n ^ 2 * Q a := by
  induction n with
  | zero => simp [QForm.Q_zero hϖ D hQ]
  | succ n ih =>
    have h2 := QForm.two_Q_eq hϖ D hQ a
    have hb := bOf_nsmul_left hϖ hQ n a a
    have e : Q (n • a + a) = Q (n • a) + Q a + bOf D.toPre Q (n • a) a := by simp only [bOf]; ring
    rw [succ_nsmul, e, ih, hb, ← h2]; push_cast; ring

theorem q_shift (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (α m : D.toPre.X) (k : ℕ) :
    Q (α + k • m) = Q α + k * (k * Q m + bOf D.toPre Q m α) := by
  have e1 : Q (α + k • m) = Q α + Q (k • m) + bOf D.toPre Q α (k • m) := by simp only [bOf]; ring
  rw [e1, QForm.bOf_comm D α (k • m), bOf_nsmul_left hϖ hQ, Q_nsmul hϖ hQ]; ring

end Q

theorem n1a : ValuationMinRepresentatives := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v hv k hk S hS s r
  refine ⟨fun h α _ => h α, fun h χ => ?_⟩
  obtain ⟨α, hα, m0, rfl⟩ := hS χ
  have H := SectionScalarValuation.fe_move hϖ hQ hv k m0 α s (h α hα)
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have e : r + (Q α : ℚ) / k + ((k * Q m0 + bOf D.toPre Q m0 α : ℤ) : ℚ) = r + (Q (α + k • m0) : ℚ) / k := by
    rw [q_shift hϖ hQ α m0 k]; push_cast; field_simp; ring
  rwa [e] at H

theorem exists_val_eq {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {r : ℚ} (hr : 0 < r) : ∃ ζ : F, ζ ≠ 0 ∧ v ζ = ((r : ℚ) : WithTop ℚ) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ ^ r.num)) r.den_pos
  have hv1 : v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ ^ r.num)) =
      ((r.num : ℚ) : WithTop ℚ) := hv _ _ ⟨1, by simp⟩
  have hpow : v (ζ ^ r.den) = r.den • v ζ := AddValuation.map_pow v ζ r.den
  rw [hζ, hv1] at hpow
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero r.den_nz
  have hne : v ζ ≠ ⊤ := by
    intro h
    rw [h, hk, succ_nsmul, WithTop.add_top] at hpow
    exact WithTop.coe_ne_top hpow
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hx, ← WithTop.coe_nsmul, WithTop.coe_eq_coe, nsmul_eq_mul] at hpow
  have hq : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  have hxr : x = r := by
    have h2 : x = (r.num : ℚ) / (r.den : ℚ) := eq_div_of_mul_eq hq (by rw [mul_comm]; exact hpow.symm)
    rw [h2, Rat.num_div_den]
  exact ⟨ζ, fun h0 => hne (by rw [h0, AddValuation.map_zero]), by rw [← hx, hxr]⟩

theorem n1c : PositiveValuationMaximalIdeal := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk s hs0
  constructor
  · rintro ⟨r, hr, hs⟩
    obtain ⟨ζ, hζ0, hvζ⟩ := exists_val_eq hv hr
    refine ⟨ζ, ζ⁻¹ • s, by rw [hvζ]; exact_mod_cast hr, ?_,
      (isSmul_iff ζ (ζ⁻¹ • s) s).2 (by rw [smul_smul, mul_inv_cancel₀ hζ0, one_smul])⟩
    have h := NuGe.smul Q (q := -r) (by rw [AddValuation.map_inv, hvζ]; rfl) ((isSmul_iff _ _ _).2 rfl) hs
    rwa [add_neg_cancel] at h
  · rintro ⟨ζ, s', hvζ, hs', hsm⟩
    obtain ⟨q, hq, hqle⟩ : ∃ q : ℚ, 0 < q ∧ ((q : ℚ) : WithTop ℚ) ≤ v ζ := by
      cases h : v ζ with
      | top => exact ⟨1, one_pos, le_top⟩
      | coe y => rw [h] at hvζ; exact ⟨y, by exact_mod_cast hvζ, le_rfl⟩
    exact ⟨0 + q, by linarith, NuGe.smul Q hqle hsm hs'⟩

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtPf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm

def SecBDvdSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (vK : AddValuation (FractionRing V) (WithTop ℚ)),
    ValOver ϖ (FractionRing V) vK →
    ∀ (k : ℕ) (α : D.toPre.X)
      (E : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))),
      VGe D (FractionRing V) vK k α E 0 → ∀ (r : V), r ≠ 0 → ∀ (f : D.toPre.SecB k α),
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) E (D.toPre.famφB α)
        (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left
        (scal (DegPre.BF D.toPre (FractionRing V)).hom r) →
      ∀ j, ∃ g : Γ(D.toPre.P.A.left, LB.wchart D.toPre.P.L (D.toPre.famφB α) j),
        f.f j = constFn D.toPre.P.A.hom _ r * g

theorem isUnit_gs_pow {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (u : Γ(X, U)ˣ) (k : ℕ) :
    IsUnit (gs f y U (u.val ^ k)) := by
  simp only [gs, dif_pos h]
  exact ((u.isUnit.pow k).map _).map _

theorem dvd_of_eq_sum {P : Scheme.{0}} {x : P} {W : P.Opens} (hmem : x ∈ W) {κ : Type} {S : Finset κ}
    {a b : κ → Γ(P, W)} {L : Γ(P, W)} (c : P.presheaf.stalk x) (heq : L = ∑ i ∈ S, a i * b i)
    (h : ∀ i ∈ S, c ∣ gs (𝟙 P) x W (a i)) : c ∣ gs (𝟙 P) x W L := by
  have hx : (𝟙 P) x ∈ W := by first | exact hmem | simpa using hmem
  subst heq
  rw [gs_fsum (𝟙 P) x W hx]
  refine Finset.dvd_sum fun i hi => ?_
  have hm : gs (𝟙 P) x W (a i * b i) = gs (𝟙 P) x W (a i) * gs (𝟙 P) x W (b i) := by
    simp only [gs, dif_pos hx, map_mul]
  rw [hm]
  exact (h i hi).mul_right _

theorem nuExt_of (hB : SecBDvdSt) : NuExtSt := by
  intro V _ _ _ ϖ hϖ D Q hQ vK hv A G _ _ _ _ _ U k hk s E hexp hnu
  obtain ⟨r, hr0, σ, f, hsσ, hEf, hexpAt⟩ := hexp
  have hvge : ∀ α, VGe D (FractionRing V) vK k α (E.s α) 0 :=
    n1e V ϖ hϖ D Q hQ (FractionRing V) vK k E hnu
  have hfd : ∀ α j, ∃ g : Γ(D.toPre.P.A.left, LB.wchart D.toPre.P.L (D.toPre.famφB α) j),
      (f α).f j = constFn D.toPre.P.A.hom _ r * g :=
    fun α => hB V ϖ hϖ D vK hv k α (E.s α) (hvge α) r hr0 (f α) (hEf α)
  choose g hg using hfd
  obtain ⟨n, hn⟩ := exists_pow_le_span hϖ hr0
  have hpw : (U.gt n).pG.left ≫ D.toPre.P.A.hom =
      pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom :=
    (Over.w (U.gt n).pG).trans pullback.condition.symm
  have hpt : ∀ (j : Fin 1 → U.LG.L.ι) (x' : ↑(pullback G.hom (thick V (maximalIdeal V) n))),
      pullback.fst G.hom (thick V (maximalIdeal V) n) x' ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j →
      cst (pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom) x' r ∣
        gs (pullback.fst G.hom (thick V (maximalIdeal V) n)) x' (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)
          (σ.f j) := by
    intro j x' hx'
    obtain ⟨S, -, hS⟩ := hexpAt n
    obtain ⟨J, hJ, -⟩ := exists_good D.toPre.P.L D.toPre.P.isLB x' (K := PEmpty) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    let pp : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) :=
      (fun _ => J (U.gt n).pG.left, fun _ => j 0)
    let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α i => J ((U.gt n).pG.left ≫ D.toPre.famφB α i)
    let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α i => J (D.toPre.Oφ (U.gt n).pG α i)
    have hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt n).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt n).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt n).pG a.1.1 a.2)))
        (Sum.elim (fun _ => pp.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
      rintro (a | a | a) (b | b | b) h <;> exact congrArg J h
    have hj0 : pullback.fst G.hom (thick V (maximalIdeal V) n) x' ∈ U.LG.L.U (j 0) := Set.mem_iInter.1 hx' 0
    have hmem : x' ∈ U.expW n pp j S jf jt := by
      refine ⟨⟨⟨Set.mem_iInter.2 fun _ => hJ _, Set.mem_iInter.2 fun _ => hj0⟩, hx'⟩, ?_⟩
      refine Finset.inf_induction (p := fun O : (thickObj V (maximalIdeal V) n G).left.Opens => x' ∈ O) trivial
        (fun a ha b hb => ⟨ha, hb⟩) (fun α _ => ⟨Set.mem_iInter.2 fun i => hJ _, Set.mem_iInter.2 fun i => hJ _⟩)
    have heq := hS pp j jf jt rfl hcoh

    have hterm : ∀ α ∈ S, ∀ (h : U.expW n pp j S jf jt ≤ (U.gt n).pG.left ⁻¹ᵁ
        LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α)),
        gs (𝟙 _) x' (U.expW n pp j S jf jt) (((thickObj V (maximalIdeal V) n G).left.presheaf.map
          (homOfLE h).op).hom (((U.gt n).pG.left.app _).hom ((f α).f (jf α)))) =
        cst (pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom) x' r *
          (show (pullback G.hom (thick V (maximalIdeal V) n)).presheaf.stalk x' from
            gs (U.gt n).pG.left x' _ (g α (jf α))) := by
      intro α _ h
      have hxα : (U.gt n).pG.left x' ∈ LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) := h hmem
      exact (gs_res (𝟙 _) x' h hmem _).trans ((gs_pull (𝟙 _) (U.gt n).pG.left x' _ hxα _).trans
        ((congrArg (fun q => gs q x' _ ((f α).f (jf α))) (Category.id_comp _)).trans
          ((congrArg (gs (U.gt n).pG.left x' _) (hg α (jf α))).trans ((gs_mul _ x' _ hxα _ _).trans
            (congrArg (· * _) ((gs_constFn D.toPre.P.A.hom _ _ x' hxα r).trans
              (congrArg (fun q => cst q x' r) hpw)))))))
    have hdv := dvd_of_eq_sum hmem (cst (pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom) x' r) heq
      (fun α _ => (dvd_mul_right _ _).trans (dvd_of_eq (hterm α.1 α.2 _).symm))
    have hdv2 := hdv.trans (dvd_of_eq (gs_mul (𝟙 _) x' _ hmem _ _))
    have hdv3 := (IsUnit.dvd_mul_left (isUnit_gs_pow (𝟙 _) x' _ hmem _ k)).1 hdv2
    exact hdv3.trans (dvd_of_eq ((gs_res (𝟙 _) x' _ hmem _).trans ((gs_pull (𝟙 _) _ x' _ hx' _).trans
      (congrArg (fun q => gs q x' _ (σ.f j)) (Category.id_comp _)))))
  obtain ⟨σ', hσ'⟩ := exists_div_sec_of_thick G.hom (maximalIdeal V ^ (n + 1)) hr0 hn σ hpt
  refine ⟨σ', SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => ?_⟩
  have h1 := secScal_sval_c hsσ (𝟙 _) y hJ
  have hm := hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (𝟙 _ ≫ pullback.fst G.hom (jK V))
  have h2 : sval σ (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
      cst ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ G.hom) y r * sval σ' (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J :=
    (congrArg (gs (𝟙 _ ≫ pullback.fst G.hom (jK V)) y _) (hσ' _)).trans ((gs_mul _ y _ hm _ _).trans
      (congrArg (· * _) (gs_constFn G.hom _ _ y hm r)))
  have hjK : ∀ a : V, (jK V).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) a) :=
    fun a => (congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))).symm
  have hcu : IsUnit (scal (pullback.snd G.hom (jK V) ≫ jK V) r) := by
    show IsUnit ((pullback.snd G.hom (jK V)).appTop.hom ((jK V).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)))
    rw [hjK]
    have hne : algebraMap V (FractionRing V) r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hr0
    exact ((isUnit_iff_ne_zero.2 hne).map _).map _
  have hceq : gs (𝟙 _) y ⊤ (scal (pullback.snd G.hom (jK V) ≫ jK V) r) =
      cst ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ G.hom) y r :=
    (gs_pull (𝟙 _) (pullback.snd G.hom (jK V) ≫ jK V) y ⊤ trivial _).trans
      (congrArg (fun q => gs q y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r))
        (by rw [Category.id_comp, Category.id_comp, pullback.condition]))
  have hgu : IsUnit (gs (𝟙 _) y ⊤ (scal (pullback.snd G.hom (jK V) ≫ jK V) r)) := by
    rw [gs_eq (𝟙 _) y ⊤ trivial]
    exact (hcu.map _).map _
  rw [hceq] at hgu
  have h3 := h2.symm.trans (h1.trans (congrArg (· * _) hceq))
  exact hgu.mul_left_cancel h3

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation QForm

def VRatioGtStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v)
      (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (m : TO hϖ hv ⟶ D.toPre.P.A), ιS hϖ hv ≫ m = p.g.b →
      ∀ (α : D.toPre.X) (G₀ : LB.Gen (LB.LinComb D.toPre.P.L (gtφO hϖ hv m α) DegPre.gtε)), G₀.IsGen → ∀ t : F,
      (∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
        (val (p.g.s α) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
          (val G₀ (r ≫ (ιS hϖ hv).left) z J).val) →
      ∃ q : ℚ, v t = (q : WithTop ℚ) ∧ (k : ℚ) * q = bOf D.toPre Q p.y α

section Ratio

variable {V : Type} [CommRing V] [IsDomain V] {F : Type} [Field F] [Algebra (FractionRing V) F] {X : Scheme.{0}}
  {L : LB X}

theorem exists_ratio (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Spec (CommRingCat.of F) ⟶ X)}
    {ε : K → ℤ} {φ' : K' → (Spec (CommRingCat.of F) ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb L φ' ε')) (ht' : t'.IsGen) (hf : FormEq φ ε φ' ε') :
    ∃ c : F, c ≠ 0 ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (J), Good L z J →
      (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * (val t' r z J).val := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of F)))) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (Spec (CommRingCat.of F))) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const L hL (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ t')) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ ht'))
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hf U h, mul_inv_cancel])
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (J), Good L z J →
      (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * (val t' r z J).val := by
    intro Z r z J hJ
    have e := ha Z r z J hJ
    rw [val_mul hJ, val_inv, Category.comp_id, ← hc] at e
    rw [← e, Units.val_mul, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]
  refine ⟨c, ?_, key⟩
  rintro rfl
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  choose I hI' using fun χ : Spec (CommRingCat.of F) ⟶ X => exists_chart hL (χ z)
  have e := key _ (𝟙 _) z I hI'
  have g0 : gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom 0) = 0 := by
    rw [map_zero]
    have := gs_add (𝟙 (Spec (CommRingCat.of F))) z ⊤ trivial (0 : Γ(Spec (CommRingCat.of F), ⊤)) 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  rw [g0, MulZeroClass.zero_mul] at e
  exact Units.ne_zero _ e

end Ratio

section Main

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem trO_one : trO hϖ hv (D := D) 1 = 𝟙 _ := by
  unfold trO
  rw [MonObj.comp_one, padd, ← Hom.mul_def, _root_.mul_one, lift_fst_snd]

theorem trO_mul (m m' : TO hϖ hv ⟶ D.toPre.P.A) : trO hϖ hv m ≫ trO hϖ hv m' = trO hϖ hv (m * m') := by
  unfold trO
  simp only [padd, ← Hom.mul_def, comp_lift, lift_fst, lift_snd, MonObj.comp_mul, lift_fst_assoc]
  rw [_root_.mul_assoc]

theorem wt_coe_of_ne {x : F} (hx : x ≠ 0) : ∃ q : ℚ, v x = (q : WithTop ℚ) := by
  have h : v x ≠ ⊤ := fun h => hx ((AddValuation.top_iff v).mp h)
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp h
  exact ⟨q, hq.symm⟩

theorem v_inv_coe {x : F} (hx : x ≠ 0) {q : ℚ} (hq : v x = q) : v x⁻¹ = ((-q : ℚ) : WithTop ℚ) := by
  rw [AddValuation.map_inv, hq]
  rfl

end Main

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
end
end

