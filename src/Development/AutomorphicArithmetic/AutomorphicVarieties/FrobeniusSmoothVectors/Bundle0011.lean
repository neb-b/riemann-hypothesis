module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOfbox
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private def diagHom {H C : Type} [Group H] [CommRing C] {n : ℕ} (m : H →* Matrix (Fin n) (Fin n) C)
    (h : ∀ s, UpT (m s)) (i : Fin n) : H →* C where
  toFun s := m s i i
  map_one' := by simp
  map_mul' s t := by
    rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h' | h'
      · rw [h s i b h', zero_mul]
      · rw [h t b i h', mul_zero]
    · simp

private def conjHom {H R : Type} [Group H] [Monoid R] (u : Rˣ) (m : H →* R) : H →* R where
  toFun s := (u : R) * m s * ((u⁻¹ : Rˣ) : R)
  map_one' := by simp
  map_mul' s t := by simp [mul_assoc]

private theorem cont_conj {X C : Type} [TopologicalSpace X] [CommRing C] {n : ℕ} (I : Ideal C)
    (m : X → Matrix (Fin n) (Fin n) C) (hm : ∀ i j, AdicCont I fun s => m s i j) (a b : Matrix (Fin n) (Fin n) C)
    (i j : Fin n) : AdicCont I fun s => (a * m s * b) i j := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) ((a * m s * b) i j)) = ∑ q, ∑ p, fun s => Ideal.Quotient.mk (I ^ N) (a i p) * Ideal.Quotient.mk (I ^ N) (m s p q) * Ideal.Quotient.mk (I ^ N) (b q j) := by
    funext s
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Finset.sum_mul, map_sum, map_mul, Finset.sum_apply]
  rw [e]
  refine Finset.sum_induction _ IsLocallyConstant (fun _ _ hf hg => hf.add hg) (IsLocallyConstant.const 0) (fun q _ => ?_)
  refine Finset.sum_induction _ IsLocallyConstant (fun _ _ hf hg => hf.add hg) (IsLocallyConstant.const 0) (fun p _ => ?_)
  exact ((IsLocallyConstant.const _).mul (hm p q N)).mul (IsLocallyConstant.const _)

theorem UpperTheory.V.Fr.pr_ofbox :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (C : Type) [CommRing C] (I : Ideal C) (B : Box F n C), (B.r F.c).mat = 1 → (∀ i j, i ≠ j → ((B.r F.g0).mat - (B.r (F.star F.g0)).mat) i j = 0) → B.Cont I → ∃ ρ : NRep F n C, B.Of ρ ∧ ρ.Cont I := by
  intro l _ k _ _ F C₀ n hF C _ I B hc hdg hcont
  let rr : F.G0 →* Matrix (Fin n) (Fin n) C := (Units.coeHom _).comp (glPart F.del B.r B.nu)
  let m : ∀ v, F.Gv v →* Matrix (Fin n) (Fin n) C := fun v => conjHom (B.g v) (rr.comp (F.loc0 v))
  have hup : ∀ v s, UpT (m v s) := fun v s => B.tri v s
  let ψ : (v : F.V) → Fin n → F.Gv v →* Cˣ := fun v i => (diagHom (m v) (hup v) i).toHomUnits
  have hpol : ∀ g : F.G0, rr (F.star g) = Jmat (R := C) n * (rr g)ᵀ * Jmat (R := C) n := by
    intro g
    have hcc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
    have hs : ((F.star g : F.G0) : F.Γ) = F.c * (↑g)⁻¹ * F.c := by
      show ((F.conj g⁻¹ : F.G0) : F.Γ) = _
      rw [Frame.conj, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, hcc]
      rfl
    have hPl : (B.r F.c).left = 1 := Units.ext hc
    have hPr : (B.r F.c).right = -1 := by rw [B.nu, hF.del_c]
    have hX : (B.r (↑g)⁻¹).left = (glPart F.del B.r B.nu g)⁻¹ := by
      rw [← map_inv]
      rfl
    show ((B.r ↑(F.star g)).left : Matrix (Fin n) (Fin n) C) = _
    rw [hs, map_mul, map_mul, SemidirectProduct.mul_left, SemidirectProduct.mul_left]
    simp only [hPl, hPr, map_one, mul_one, one_mul, sgnAct_neg_one, hX, theta_val, inv_inv]
    rfl
  have hord : ∀ v (g : Fin n → F.Gv v), ordProd (fun s => rr (F.loc0 v s)) (fun i s => ((ψ v i s : Cˣ) : C)) g = 0 := by
    intro v g
    have hf : UpperTheory.V.W.HasFlag (rr.comp (F.loc0 v)).toHomUnits (ψ v) := ⟨B.g v, fun s => ⟨fun i j hij => hup v s i j hij, fun i => rfl⟩⟩
    exact (ord_of_flag (rr.comp (F.loc0 v)) (ψ v) hf).1 g
  refine ⟨⟨rr, ψ, hpol, fun i j hij => hdg i j hij, hord⟩, ⟨hc, fun s => rfl, fun v i s => rfl⟩, ?_, ?_⟩
  · intro i j N
    exact (hcont i j N).comp_continuous continuous_subtype_val
  · intro v i
    exact cont_conj I (fun s => (B.r (F.loc v s)).mat) (fun p q N => (hcont p q N).comp_continuous (continuous_subtype_val.comp (hF.loc_cont v))) ↑(B.g v) ↑(B.g v)⁻¹ i i
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOpen
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_open :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Box F n R), B.Cont (maximalIdeal R) → IsOpen ((B.bar O).r.ker : Set F.Γ) ∧ IsOpen ((B.bar O).ad.ker : Set F.Γ) ∧ IsLocallyConstant fun s => ((B.bar O).r s).mat := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ B hB
  have hent : ∀ i j, IsLocallyConstant fun s => ((B.bar O).r s).mat i j := fun i j => by
    have hk : ∀ a ∈ maximalIdeal R ^ 1, (res O R : R →+* ResidueField O) a = 0 := fun a ha => by
      rw [pow_one] at ha
      exact (res_eq_zero_iff O R a).2 ha
    exact (hB i j 1).comp (Ideal.Quotient.lift _ (res O R : R →+* ResidueField O) hk)
  have hmat : IsLocallyConstant fun s => ((B.bar O).r s).mat := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have h : ∀ᶠ y in nhds x, ∀ i j, ((B.bar O).r y).mat i j = ((B.bar O).r x).mat i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hent i j).eventually_eq x
    exact h.mono fun y hy => Matrix.ext hy
  have hr : IsOpen ((B.bar O).r.ker : Set F.Γ) := by
    have e : ((B.bar O).r.ker : Set F.Γ) =
        {s | ((B.bar O).r s).mat = 1} ∩ (F.del.ker : Set F.Γ) := by
      ext s
      constructor
      · intro hs
        have hs' : (B.bar O).r s = 1 := hs
        refine ⟨?_, ?_⟩
        · show ((B.bar O).r s).mat = 1
          rw [hs']
          rfl
        · show F.del s = 1
          rw [← (B.bar O).nu s, hs']
          rfl
      · rintro ⟨h1, h2⟩
        show (B.bar O).r s = 1
        refine SemidirectProduct.ext (Units.ext h1) ?_
        rw [(B.bar O).nu s]
        exact h2
    rw [e]
    exact (hmat.isOpen_fiber 1).inter hF.del_open
  refine ⟨hr, Subgroup.isOpen_mono (fun s hs => ?_) hr, hmat⟩
  have hs' : (B.bar O).r s = 1 := hs
  show GG.ad n (ResidueField O) ((B.bar O).r s) = 1
  rw [hs', map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrSqz
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_sqz :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (n : ℕ) (μ : ResidueField O →+ C), IsSq O μ → ∃ e : Matrix (Fin n) (Fin n) (ResidueField O) → GL (Fin n) C, (∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ) ∧ (∀ X Y, e (X + Y) = e X * e Y) ∧ (∀ X, (e X)⁻¹ = e (-X)) ∧ (∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)), A * X.map μ = (A.map (res O C) * X).map μ ∧ X.map μ * A = (X * A.map (res O C)).map μ) ∧ ∀ (x : GG (m := n) (R := C)) (X : Matrix (Fin n) (Fin n) (ResidueField O)), x * GG.ofGL (e X) = GG.ofGL (e ((GG.map (res O C : C →+* ResidueField O) x).adFun X)) * x := by
  intro O _ _ C _ _ _ n μ hμ
  have hsq : ∀ c d, μ c * μ d = 0 := by
    intro c d
    have h := hμ.mul (μ c) d
    rw [(res_eq_zero_iff O C _).2 (hμ.mem c), zero_mul, map_zero] at h
    exact h.symm
  have hL : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)),
      A * X.map μ = (A.map (res O C) * X).map μ := by
    intro A X
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, hμ.mul]
  have hR : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)),
      X.map μ * A = (X * A.map (res O C)).map μ := by
    intro A X
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (X i k), hμ.mul, mul_comm]
  have hsqM : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O), X.map μ * Y.map μ = 0 := by
    intro X Y
    ext i j
    simp [Matrix.mul_apply, hsq]
  have hadd : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O), (X + Y).map μ = X.map μ + Y.map μ := by
    intro X Y
    ext i j
    simp
  have hzero : (0 : Matrix (Fin n) (Fin n) (ResidueField O)).map μ = 0 := by
    ext i j
    simp
  have hu : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O),
      (1 + X.map μ) * (1 + Y.map μ) = 1 + (X + Y).map μ := by
    intro X Y
    rw [hadd, show (1 + X.map μ) * (1 + Y.map μ) = 1 + (X.map μ + Y.map μ) + X.map μ * Y.map μ by
      noncomm_ring, hsqM, add_zero]
  let e : Matrix (Fin n) (Fin n) (ResidueField O) → GL (Fin n) C := fun X =>
    ⟨1 + X.map μ, 1 + (-X).map μ, by rw [hu, add_neg_cancel, hzero, add_zero],
      by rw [hu, neg_add_cancel, hzero, add_zero]⟩
  have he : ∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ := fun X => rfl
  have hemul : ∀ X Y, e (X + Y) = e X * e Y := by
    intro X Y
    apply Units.ext
    rw [Units.val_mul, he, he, he, hu]
  have heinv : ∀ X, (e X)⁻¹ = e (-X) := fun X => Units.ext rfl
  have hconj : ∀ (g : GL (Fin n) C) (h : GL (Fin n) (ResidueField O))
      (Y : Matrix (Fin n) (Fin n) (ResidueField O)),
      (g : Matrix (Fin n) (Fin n) C).map (res O C) = (h : Matrix (Fin n) (Fin n) (ResidueField O)) →
      g * e Y = e ((h : Matrix (Fin n) (Fin n) (ResidueField O)) * Y *
        (↑h⁻¹ : Matrix (Fin n) (Fin n) (ResidueField O))) * g := by
    intro g h Y hh
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he, he, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, hL, hR, hh, Matrix.mul_assoc ((h : Matrix (Fin n) (Fin n) (ResidueField O)) * Y),
      Units.inv_mul, Matrix.mul_one]
  have hJ : (Jmat (R := C) n).map (res O C) = Jmat (R := ResidueField O) n :=
    Jmat_map (res O C : C →+* ResidueField O) n
  have htheta : ∀ Y, theta (e Y) = e (thetaLie Y) := by
    intro Y
    apply Units.ext
    rw [theta_val, heinv, he, he, Matrix.transpose_add, Matrix.transpose_one, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Jmat_mul_Jmat, ← Matrix.transpose_map, hL, hJ, hR, hJ]
    rw [show thetaLie Y = Jmat (R := ResidueField O) n * (-Y)ᵀ * Jmat (R := ResidueField O) n by
      simp [thetaLie, Matrix.transpose_neg]]
  refine ⟨e, he, hemul, heinv, fun A X => ⟨hL A X, hR A X⟩, ?_⟩
  intro x X
  obtain ⟨g, s⟩ := x
  have hh : (g : Matrix (Fin n) (Fin n) C).map (res O C) =
      ((GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG (m := n) (R := C))).left :
        Matrix (Fin n) (Fin n) (ResidueField O)) := rfl
  have had : GG.adFun (GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG (m := n) (R := C))) X =
      ((GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG (m := n) (R := C))).left :
        Matrix (Fin n) (Fin n) (ResidueField O)) *
        (if s = 1 then X else thetaLie X) *
        (↑(GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG (m := n) (R := C))).left⁻¹ :
          Matrix (Fin n) (Fin n) (ResidueField O)) := rfl
  rw [had]
  refine SemidirectProduct.ext ?_ ?_
  · simp only [GG.ofGL, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply]
    rcases Int.units_eq_one_or s with rfl | rfl
    · rw [sgnAct_one, ite_eq_left rfl]
      exact hconj _ _ X hh
    · rw [sgnAct_neg_one, ite_eq_right (by decide), htheta]
      exact hconj _ _ _ hh
  · simp only [GG.ofGL, SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SgWeight
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zcases (j : ZMod 2) : j = 0 ∨ j = 1 := by
  revert j; decide

private theorem sg0 (K : Type) [CommRing K] : sg K 0 = 1 := by simp [sg]

private theorem sg1 (K : Type) [CommRing K] : sg K 1 = -1 := by
  show (-1 : K) ^ ((1 : ZMod 2).val) = -1
  rw [show (1 : ZMod 2).val = 1 from rfl]
  simp

private theorem sg_add (K : Type) [CommRing K] (i j : ZMod 2) : sg K (i + j) = sg K i * sg K j := by
  rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl
  · simp [sg0]
  · simp [sg0]
  · simp [sg0]
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, sg0, sg1]
    ring

private theorem sg_nsmul (K : Type) [CommRing K] (m : ℕ) (i : ZMod 2) : sg K (m • i) = sg K i ^ m := by
  induction m with
  | zero => simp [sg0]
  | succ k ih => rw [succ_nsmul, sg_add, ih, pow_succ]

private theorem sg_weight (K : Type) [CommRing K] {ι : Type} (wt : ι → ZMod 2) (n : ι →₀ ℕ) :
    (n.prod fun s m => sg K (wt s) ^ m) = sg K (Finsupp.weight wt n) := by
  classical
  rw [Finsupp.weight_apply]
  simp only [Finsupp.prod, Finsupp.sum, ← sg_nsmul]
  generalize n.support = t
  refine Finset.induction_on t ?_ ?_
  · simp [sg0]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, sg_add]

private theorem coeff_sg (O : Type) [CommRing O] {ι : Type} (j : ZMod 2) (y : MvPowerSeries ι O) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (sg _ j * y) = sg O j * MvPowerSeries.coeff n y := by
  rcases zcases j with rfl | rfl <;> simp [sg0, sg1]

theorem UpperTheory.V.Fr.ep_ps :
    ∀ (O : Type) [CommRing O], IsUnit (2 : O) → ∀ (ι : Type) [Finite ι] (wt : ι → ZMod 2), ∃ τ : MvPowerSeries ι O →ₐ[O] MvPowerSeries ι O, (∀ y, τ (τ y) = y) ∧ (∀ j, evp τ j = wtPart O wt j) ∧ ∀ j y, (2 : MvPowerSeries ι O) * wcomp O wt j y = y + sg _ j * τ y := by
  classical
  intro O _ h2 ι _ wt
  have hsq : ∀ i : ZMod 2, sg O i * sg O i = 1 := by
    intro i
    rw [← sg_add]
    rcases zcases i with rfl | rfl
    · exact sg0 O
    · rw [show (1 : ZMod 2) + 1 = 0 from rfl]
      exact sg0 O
  have hne : ∀ i j : ZMod 2, i ≠ j → sg O i = - sg O j := by
    intro i j hij
    rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl
    · exact absurd rfl hij
    · simp [sg0, sg1]
    · simp [sg0, sg1]
    · exact absurd rfl hij
  let a : ι → O := fun s => sg O (wt s)
  have hcoef : ∀ y n, MvPowerSeries.coeff n (MvPowerSeries.rescale a y)
      = sg O (Finsupp.weight wt n) * MvPowerSeries.coeff n y := by
    intro y n
    rw [MvPowerSeries.coeff_rescale, sg_weight]
  let τ : MvPowerSeries ι O →ₐ[O] MvPowerSeries ι O :=
    AlgHom.mk (MvPowerSeries.rescale a) (fun r => by
      ext n
      show MvPowerSeries.coeff n (MvPowerSeries.rescale a (algebraMap O _ r)) = _
      rw [hcoef]
      by_cases hn : n = 0
      · subst hn
        simp [sg0]
      · classical
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          MvPowerSeries.coeff_C, if_neg hn, mul_zero])
  have hτ : ∀ y n, MvPowerSeries.coeff n (τ y)
      = sg O (Finsupp.weight wt n) * MvPowerSeries.coeff n y := hcoef
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro y
    ext n
    rw [hτ, hτ, ← mul_assoc, hsq, one_mul]
  · intro j
    ext y
    show τ y = sg _ j * y ↔ ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n y = 0
    constructor
    · intro h n hn
      have := congrArg (MvPowerSeries.coeff n) h
      rw [hτ, coeff_sg, hne _ _ hn] at this
      have h' : 2 * MvPowerSeries.coeff n y = 0 := by
        linear_combination (-sg O j) * this - (2 * MvPowerSeries.coeff n y) * hsq j
      exact (h2.mul_right_eq_zero).mp h'
    · intro h
      ext n
      rw [hτ, coeff_sg]
      by_cases hn : Finsupp.weight wt n = j
      · rw [hn]
      · rw [h n hn, mul_zero, mul_zero]
  · intro j y
    ext n
    rw [two_mul, map_add (f := _), coeff_wcomp, map_add (f := _), coeff_sg, hτ]
    split_ifs with hn
    · rw [hn]
      linear_combination (-MvPowerSeries.coeff n y) * hsq j
    · rw [hne _ _ hn]
      linear_combination MvPowerSeries.coeff n y * hsq j
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SgZero
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_zero (R : Type) [CommRing R] : sg R 0 = 1 := by simp [sg]

private theorem sg_one (R : Type) [CommRing R] : sg R 1 = -1 := by
  show (-1 : R) ^ (1 : ZMod 2).val = -1
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

theorem UpperTheory.V.Fr.ep_ee :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), S.u.ee ≤ x → ∀ σ, L.IsInv σ → L.ρ.ee = Ideal.span (evp σ 1 : Set L.R) := by
  intro l _ O _ _ _ _ F C₀ hF S x L hx σ hσ
  have hl : l ≠ 2 := hF.l_odd
  have h2O : IsUnit (2 : L.O') := by
    by_contra h
    have hm : (2 : L.O') ∈ maximalIdeal L.O' := (mem_maximalIdeal _).mpr h
    have hr : residue L.O' 2 = 0 := (residue_eq_zero_iff _).mpr hm
    rw [map_ofNat] at hr
    have hd : l ∣ 2 := (CharP.cast_eq_zero_iff (ResidueField L.O') l 2).mp (by exact_mod_cast hr)
    have hp : l.Prime := Fact.out
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hl h1
  have h2 : IsUnit (2 : L.R) := by
    have := h2O.map (algebraMap L.O' L.R)
    rw [map_ofNat] at this
    exact this
  have hpw : ∀ a b : Fin 3, Odd (w 3 a - w 3 b) → pw a b = 1 := by
    intro a b h
    obtain ⟨k, hk⟩ := h
    show ((w 3 a - w 3 b : ℤ) : ZMod 2) = 1
    rw [hk, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat,
      show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  have hpw0 : ∀ a b : Fin 3, Even (w 3 a - w 3 b) → pw a b = 0 := by
    intro a b h
    obtain ⟨k, hk⟩ := h
    show ((w 3 a - w 3 b : ℤ) : ZMod 2) = 0
    rw [hk, ← two_mul, Int.cast_mul, Int.cast_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  apply le_antisymm
  · unfold NRep.ee
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨g, i, j, hodd, rfl⟩
    apply Ideal.subset_span
    have he := hσ.ent g i j
    rw [hpw i j hodd] at he
    exact he
  · refine Ideal.span_le.mpr ?_
    intro y hy
    have hy' : σ y = sg L.R 1 * y := hy
    rw [sg_one] at hy'
    have hIm : L.ρ.ee ≤ maximalIdeal L.R := by
      unfold NRep.ee
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨g, i, j, hodd, rfl⟩
      have hmem : S.u.r g i j ∈ S.u.ee := Ideal.subset_span ⟨g, i, j, hodd, rfl⟩
      have hxm := hx hmem
      rw [← L.lies] at hxm
      exact Ideal.mem_comap.mp hxm
    haveI : Nontrivial (L.R ⧸ L.ρ.ee) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal L.R).ne_top hIm)
    haveI : IsCO L.O' (L.R ⧸ L.ρ.ee) :=
      co_quot L.O' L.R _ (Ideal.Quotient.mkₐ L.O' L.ρ.ee) (Ideal.Quotient.mkₐ_surjective _ _)
    have key' : ∀ z (hz : z ∈ Algebra.adjoin O ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j})),
        Ideal.Quotient.mk L.ρ.ee (σ (L.ι ⟨z, hz⟩)) = Ideal.Quotient.mk L.ρ.ee (L.ι ⟨z, hz⟩) := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
        rcases hz with hB | ⟨g, i, j, rfl⟩
        · have hb' : σ (L.b ⟨z, hB⟩) = sg L.R 0 * L.b ⟨z, hB⟩ := hσ.base ⟨z, hB⟩
          rw [sg_zero, one_mul] at hb'
          show Ideal.Quotient.mk _ (σ (L.b ⟨z, hB⟩)) = Ideal.Quotient.mk _ (L.b ⟨z, hB⟩)
          rw [hb']
        · have he' : σ (L.ρ.r g i j) = sg L.R (pw i j) * L.ρ.r g i j := hσ.ent g i j
          show Ideal.Quotient.mk _ (σ (L.ρ.r g i j)) = Ideal.Quotient.mk _ (L.ρ.r g i j)
          rcases Int.even_or_odd (w 3 i - w 3 j) with h | h
          · rw [hpw0 i j h, sg_zero, one_mul] at he'
            rw [he']
          · rw [hpw i j h, sg_one] at he'
            have hm : L.ρ.r g i j ∈ L.ρ.ee := Ideal.subset_span ⟨g, i, j, h, rfl⟩
            rw [he', Ideal.Quotient.eq]
            have hc : -1 * L.ρ.r g i j - L.ρ.r g i j = (-2) * L.ρ.r g i j := by ring
            rw [hc]
            exact Ideal.mul_mem_left _ _ hm
      | algebraMap r =>
        show Ideal.Quotient.mk _ (σ (L.ι (algebraMap O S.A r))) = Ideal.Quotient.mk _ (L.ι (algebraMap O S.A r))
        rw [L.ι.commutes]
        have hc := (σ.restrictScalars O).commutes r
        rw [AlgHom.restrictScalars_apply] at hc
        rw [hc]
      | add a b ha hb iha ihb =>
        show Ideal.Quotient.mk _ (σ (L.ι (⟨a, ha⟩ + ⟨b, hb⟩))) = Ideal.Quotient.mk _ (L.ι (⟨a, ha⟩ + ⟨b, hb⟩))
        simp only [map_add (f := _), iha, ihb]
      | mul a b ha hb iha ihb =>
        show Ideal.Quotient.mk _ (σ (L.ι (⟨a, ha⟩ * ⟨b, hb⟩))) = Ideal.Quotient.mk _ (L.ι (⟨a, ha⟩ * ⟨b, hb⟩))
        simp only [map_mul, iha, ihb]
    have huniq := L.univ (L.R ⧸ L.ρ.ee) ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) (fun a => by
      show res L.O' _ (Ideal.Quotient.mkₐ L.O' L.ρ.ee (L.ι a)) = _
      exact res_map _ _)
    have h1 : ∀ a : S.A, ((Ideal.Quotient.mkₐ L.O' L.ρ.ee).comp σ) (L.ι a) =
        ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) a := by
      rintro ⟨z, hz⟩
      exact key' z hz
    have h2' : ∀ a : S.A, (Ideal.Quotient.mkₐ L.O' L.ρ.ee) (L.ι a) =
        ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) a := fun a => rfl
    have heq := huniq.unique h1 h2'
    have hyq := AlgHom.congr_fun heq y
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hy'] at hyq
    have hd := Ideal.Quotient.eq.mp hyq
    have h2y : 2 * y ∈ L.ρ.ee := by
      have hc : 2 * y = -((-1 * y) - y) := by ring
      rw [hc]
      exact neg_mem hd
    obtain ⟨u, hu⟩ := h2
    have hc : y = (↑u⁻¹ : L.R) * (2 * y) := by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    show y ∈ L.ρ.ee
    rw [hc]
    exact Ideal.mul_mem_left _ _ h2y
end

