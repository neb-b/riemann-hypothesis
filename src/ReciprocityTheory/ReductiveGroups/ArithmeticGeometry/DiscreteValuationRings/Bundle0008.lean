module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CubicNormMulIdentity
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem four (h : IsCub θ) (P q B b x : A) :
    θ (P * B) (q * b) x * θ P B x * θ q b x = θ (P * q) (B * b) x * θ P q x * θ B b x := by
  have c1 := h.coc P B (q * b) x
  have c2 := h.coc B q b x
  have c3 := h.coc P q (B * b) x
  have c4 := h.coc q B b x
  rw [mul_left_comm B q b] at c1
  rw [mul_comm q B, h.s01 q B x] at c4
  calc θ (P * B) (q * b) x * θ P B x * θ q b x
      = θ P (q * (B * b)) x * (θ B (q * b) x * θ q b x) := by rw [c1, mul_assoc]
    _ = θ P (q * (B * b)) x * (θ q (B * b) x * θ B b x) := by rw [← c2, c4]
    _ = θ (P * q) (B * b) x * θ P q x * θ B b x := by rw [c3, mul_assoc]

theorem cubic_norm_mul_identity (h : IsCub θ) (k : ℕ) (B b x : A) :
    θ (B ^ k) (b ^ k) x * cubN θ k 1 B x * cubN θ k 1 b x = cubN θ k 1 (B * b) x * θ B b x ^ k := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have f := four h (B ^ k) (b ^ k) B b x
    simp only [cubN, one_mul] at ih ⊢
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, pow_succ B, pow_succ b,
      pow_succ (θ B b x), mul_pow]
    apply mul_right_cancel (b := θ (B ^ k) (b ^ k) x)
    calc _ = (θ (B ^ k * B) (b ^ k * b) x * θ (B ^ k) B x * θ (b ^ k) b x) *
          (θ (B ^ k) (b ^ k) x * (∏ i ∈ Finset.range k, θ (B ^ i) B x) *
            ∏ i ∈ Finset.range k, θ (b ^ i) b x) := by ac_rfl
      _ = _ := by rw [f, ih]; ac_rfl

theorem cubN_mul (h : IsCub θ) (k : ℕ) (a B b x : A) :
    cubN θ k a B x * cubN θ k (a * B ^ k) b x * (θ B x b ^ k)⁻¹ = cubN θ k a (B * b) x := by
  have e1 := cubic_norm_mul_identity h k B b x
  have c := h.coc a (B ^ k) (b ^ k) x
  rw [h.N_split k a B x, h.N_split k (a * B ^ k) b x, h.N_split k a (B * b) x, mul_pow, h.s12 B x b]
  apply mul_right_cancel (b := θ (B ^ k) (b ^ k) x * θ B b x ^ k)
  calc _ = (θ (a * B ^ k) (b ^ k) x * θ a (B ^ k) x) *
        (θ (B ^ k) (b ^ k) x * cubN θ k 1 B x * cubN θ k 1 b x) * ((θ B b x ^ k)⁻¹ * θ B b x ^ k) := by
        ac_rfl
    _ = (θ a (B ^ k * b ^ k) x * θ (B ^ k) (b ^ k) x) * (cubN θ k 1 (B * b) x * θ B b x ^ k) := by
        rw [c, e1, inv_mul_cancel, mul_one]
    _ = _ := by ac_rfl

theorem hv_comp (h : IsCub θ) (k : ℕ) (a B b x : A) :
    hv θ k a B (x * b) * hv θ k (a * B ^ k) b x = hv θ k a (B * b) x * hv θ k a B b := by
  have n := h.N_add k a B x b
  have m := cubN_mul h k a B b x
  have t : ∀ u v, θ a u v = θ u v a := fun u v => (h.s01 a u v).trans (h.s12 u a v)
  have key : θ a x b * θ a (x * b) B = θ a x (B * b) * θ a b B := by
    have c := h.coc x b B a
    rw [t x b, t (x * b) B, t x (B * b), t b B, mul_comm B b, mul_comm (θ x b a)]
    exact c
  simp only [hv]
  apply mul_right_cancel (b := θ a x b * θ a (x * b) B * θ (a * B ^ k) x b * θ B x b ^ k)
  rw [← m]
  calc _ = (cubN θ k a B (x * b) * θ a x b * θ B x b ^ k) * cubN θ k (a * B ^ k) b x *
        ((θ a (x * b) B)⁻¹ * θ a (x * b) B) * ((θ (a * B ^ k) x b)⁻¹ * θ (a * B ^ k) x b) := by ac_rfl
    _ = θ (a * B ^ k) x b * cubN θ k a B x * cubN θ k a B b * cubN θ k (a * B ^ k) b x := by
        rw [n, inv_mul_cancel, inv_mul_cancel, mul_one, mul_one]
    _ = (cubN θ k a B x * cubN θ k (a * B ^ k) b x * cubN θ k a B b * θ (a * B ^ k) x b) *
        ((θ B x b ^ k)⁻¹ * θ B x b ^ k) * ((θ a x (B * b))⁻¹ * θ a x (B * b)) * ((θ a b B)⁻¹ * θ a b B) := by
        rw [inv_mul_cancel, inv_mul_cancel, inv_mul_cancel, mul_one, mul_one, mul_one]; ac_rfl
    _ = _ := by rw [key]; ac_rfl

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtA
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Out

section Dvr

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem exists_pow_le_span {ϖ : V} (hϖ : Irreducible ϖ) {r : V} (hr : r ≠ 0) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal V ^ (n + 1) ≤ Ideal.span {r} := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  refine ⟨n, ?_⟩
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow, hu,
    Ideal.span_singleton_mul_left_unit u.isUnit]
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ n))

theorem mem_range_of_val_nonneg {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation (FractionRing V) (WithTop ℚ)}
    (hv : ValOver ϖ (FractionRing V) v) (c : FractionRing V) (hc : 0 ≤ v c) :
    c ∈ (algebraMap V (FractionRing V)).range := by
  classical
  by_cases hc0 : c = 0
  · exact ⟨0, by rw [hc0, map_zero]⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) c
  have ha : a ≠ 0 := by
    rintro rfl
    exact hc0 (by simp)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n1, u1, hu1⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨n2, u2, hu2⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero))
  have hu2' : algebraMap V (FractionRing V) (u2 : V) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero u2.ne_zero)
  set w : Vˣ := u1 * u2⁻¹ with hw
  have hval : HasVal ϖ (algebraMap V (FractionRing V) a / algebraMap V (FractionRing V) b) ((n1 : ℤ) - n2) := by
    refine ⟨w, ?_⟩
    rw [hu1, hu2, hw, zpow_sub₀ hϖ0, zpow_natCast, zpow_natCast]
    simp only [map_mul, map_pow, Units.val_mul]
    have hinv : algebraMap V (FractionRing V) ((u2⁻¹ : Vˣ) : V) = (algebraMap V (FractionRing V) (u2 : V))⁻¹ := by
      exact map_units_inv (algebraMap V (FractionRing V)) u2
    rw [hinv]
    field_simp
  have hv1 := hv _ _ hval
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hv1
  rw [hv1] at hc
  have hn : (0 : ℤ) ≤ (n1 : ℤ) - n2 := by
    have : ((0 : ℚ) : WithTop ℚ) ≤ (((n1 : ℤ) - n2 : ℤ) : ℚ) := by simpa using hc
    have h2 : (0 : ℚ) ≤ (((n1 : ℤ) - n2 : ℤ) : ℚ) := WithTop.coe_le_coe.mp this
    exact_mod_cast h2
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hn
  obtain ⟨w', hw'⟩ := hval
  refine ⟨ϖ ^ k * (w' : V), ?_⟩
  rw [hw', hk, zpow_natCast, map_mul, map_pow]

variable {X : Scheme.{0}}

theorem isUnit_cst (p : X ⟶ Sp V) (x : X) {r : V} (hx : r ∉ (p x).asIdeal) : IsUnit (cst p x r) := by
  have hmem : p x ∈ (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) := by
    have e := basicOpen_eq_of_affine (R := CommRingCat.of V) r
    exact (congrArg (fun U : (Sp V).Opens => p x ∈ U) e).mpr hx
  have e2 := Scheme.preimage_basicOpen p ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)
  have hx' : x ∈ X.basicOpen ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)) := by
    rw [← e2]; exact hmem
  have hu := (Scheme.mem_basicOpen X ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)) x
    (show x ∈ p ⁻¹ᵁ ⊤ from trivial)).1 hx'
  rw [cst, gs_eq p x ⊤ (show p x ∈ (⊤ : (Sp V).Opens) from trivial)]
  exact hu

theorem exists_fst_eq (p : X ⟶ Sp V) (J : Ideal V) {r : V} (hJ : J ≤ Ideal.span {r}) (x : X)
    (hx : r ∈ (p x).asIdeal) :
    ∃ x', pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' = x := by
  have h1 : x ∈ Set.range (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) := by
    rw [Scheme.Pullback.range_fst]
    show p x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J))
    rw [range_comap_of_surjective (V ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact fun y hy => (Ideal.span_singleton_le_iff_mem _).2 hx (hJ hy)
  exact h1

theorem exists_div_sec_of_thick (p : X ⟶ Sp V) [Flat p] (J : Ideal V) {r : V} (hr : r ≠ 0)
    (hJ : J ≤ Ideal.span {r}) {M : LB X} (s : LB.Sec M)
    (h : ∀ j (x' : ↑(pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))),
      pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' ∈ M.U j →
      cst (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ p) x' r ∣
        gs (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) x' (M.U j) (s.f j)) :
    ∃ s' : LB.Sec M, ∀ j, s.f j = constFn p _ r * s'.f j := by
  refine exists_div_sec p hr s fun j x hx => ?_
  by_cases hxr : r ∈ (p x).asIdeal
  · obtain ⟨x', rfl⟩ := exists_fst_eq p J hJ x hxr
    exact dvd_germ_of_thick p J hJ (s.f j) x' hx (h j x' hx)
  · exact (isUnit_cst p x hxr).dvd

end Dvr

section Sec

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem secScal_sval_c {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have hc : LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k))
      (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e
  have e := H _ _ hc
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  exact ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans
    ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top hm c) (gs_res r z _ hm _))))

end Sec

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Cube

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def cQ (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

theorem cQ_add (T : Over (Spec (CommRingCat.of R))) (a b : D.X) : cQ D T (a + b) = cQ D T a * cQ D T b := by
  unfold cQ
  rw [D.c_add, padd, ← Hom.mul_def, MonObj.comp_mul]

theorem cQ_nsmul (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (a : D.X) : cQ D T (k • a) = cQ D T a ^ k := by
  induction k with
  | zero =>
    rw [zero_smul, pow_zero]
    have h0 : cQ D T 0 * cQ D T 0 = cQ D T 0 := by rw [← cQ_add, add_zero]
    simpa using h0
  | succ k ih => rw [succ_nsmul, cQ_add, ih, pow_succ]

theorem comp_cQ {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (a : D.X) : ρ ≫ cQ D T a = cQ D T' a := by
  unfold cQ
  rw [← Category.assoc, toUnit_unique (ρ ≫ toUnit T) (toUnit T')]

theorem prod_famB {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ D.P.A) (χ : D.X) (k : ℕ) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ D.famφB χ i) ^ DegPre.famε k i =
      h ρ.left ^ ((k : ℤ) - 1) * h (ρ * cQ D T χ).left * (h (cQ D T χ).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have e1 : ρ.left ≫ (𝟙 D.P.A.left) = ρ.left := Category.comp_id _
  have e2 : ρ.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c χ)).left = (ρ * cQ D T χ).left := by
    rw [← Over.comp_left]
    congr 1
    rw [padd, Hom.mul_def, comp_lift_assoc, Category.comp_id, cQ, ← Category.assoc, comp_toUnit]
  have e3 : ρ.left ≫ (toUnit D.P.A ≫ D.c χ).left = (cQ D T χ).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
    rfl
  have e4 : ρ.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (1 : T ⟶ D.P.A).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit, Hom.one_def]
  rw [Fin.prod_univ_four]
  simp only [DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpow_one, zpow_neg, e1, e2, e3, e4]

theorem prod_neg' {K U : Type} [Fintype K] [CommGroup U] (f : K → U) (e : K → ℤ) {c : U} (h : ∏ i, f i ^ e i = c) :
    ∏ i, f i ^ (-e i) = c⁻¹ := by
  simp only [zpow_neg, Finset.prod_inv_distrib, h]

theorem exists_eB (k : ℕ) (α mu : D.X) {Ix : Type} [Fintype Ix]
    {φV : Ix → (Spec (CommRingCat.of R) ⟶ D.P.A.left)} {εV : Ix → ℤ}
    (w : LB.Gen (LB.LinComb D.P.L φV εV)) (hw : w.IsGen)
    (hC : ∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U), ∏ i, h (D.P.A.hom ≫ φV i) ^ εV i =
      (h (cQ D D.P.A α * cQ D D.P.A mu).left)⁻¹ * h (cQ D D.P.A α).left * h (cQ D D.P.A mu).left *
        (h (1 : D.P.A ⟶ D.P.A).left)⁻¹ * (h (cQ D D.P.A mu).left ^ k)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ k) :
    ∃ eB : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (α + k • mu))
        (fun i => (𝟙 D.P.A * cQ D D.P.A mu).left ≫ D.famφB α i)) (DegPre.deltaε k)), eB.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        val eB ρ.left z J = cubN (cubV D.cub z J) k (cQ D T α) (cQ D T mu) ρ *
          (cubV D.cub z J (cQ D T α) ρ (cQ D T mu))⁻¹ * val w (ρ.left ≫ D.P.A.hom) z J := by
  set a : D.P.A ⟶ D.P.A := cQ D _ α with ha
  set m : D.P.A ⟶ D.P.A := cQ D _ mu with hm
  have hα' : cQ D D.P.A (α + k • mu) = a * m ^ k := by rw [cQ_add, cQ_nsmul]
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a m (𝟙 D.P.A) k
  obtain ⟨e, he, ve⟩ := exists_gen D.P.isLB (φ' := Sum.elim (D.famφB (α + k • mu))
      (fun i => (𝟙 D.P.A * m).left ≫ D.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a (𝟙 D.P.A) m h
      have p₂ := hC U h
      have p₃ := prod_famB D (𝟙 _) (α + k • mu) k h
      have p₄ := prod_famB D (𝟙 D.P.A * m) α k h
      have e₃ : ∀ i, Over.Hom.left (𝟙 D.P.A) ≫ D.famφB (α + k • mu) i = D.famφB (α + k • mu) i := fun i => by simp
      simp only [e₃] at p₃
      rw [hα'] at p₃
      rw [← ha] at p₄
      have q₁ : 𝟙 D.P.A * (a * m ^ k) = a * m ^ k * 𝟙 D.P.A := mul_comm _ _
      have q₂ : 𝟙 D.P.A * m * a = a * 𝟙 D.P.A * m := by rw [mul_comm _ a, ← _root_.mul_assoc]
      have q₃ : m * 𝟙 D.P.A = 𝟙 D.P.A * m := mul_comm _ _
      rw [q₁] at p₃
      rw [q₂] at p₄
      have S : ∀ {K K' : Type} {_ : Fintype K} {_ : Fintype K'} (f : K ⊕ K' → U),
          ∏ i, f i = (∏ i, f (.inl i)) * ∏ i, f (.inr i) := fun f => Fintype.prod_sum_type f
      rw [S, S]
      erw [S]
      simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε]
      erw [prod_neg' _ _ p₁]
      rw [p₂, p₃, prod_neg' _ _ p₄]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, q₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift (𝟙 D.P.A) m)).left)))
      (LB.pullGen D.P.L _ _ w D.P.A.hom))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))) (pullGen_isGen _ _ _ _ hw _))
  refine ⟨e, he, fun T ρ z J hJ => ?_⟩
  have E := (ve _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vN T ρ z J hJ)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _))))) (val_pull hJ _ _ _)))
  refine E.trans ?_
  rw [ha, hm, comp_cQ, comp_cQ, Category.comp_id]

end Cube

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
end
end

