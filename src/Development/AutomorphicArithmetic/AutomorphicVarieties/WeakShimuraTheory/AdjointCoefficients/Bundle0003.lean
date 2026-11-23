module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ExistsStrictHenselianAbsolutelyClosedLocalRing
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem exists_strictHenselian_absolutely_closed_local_ring {k A : Type} [CommRing k] [CommRing A] (π : A → k) (μ : k → A)
    (h1 : ∀ c d, μ (c + d) = μ c + μ d) (h2 : ∀ (a : A) c, μ (π a * c) = a * μ c) :
    ∃ T : M4 k →+ M4 A, (∀ Y, Y.map μ = T Y) ∧
      (∀ (M : M4 A) Y, M * T Y = T (M.map π * Y)) ∧
      (∀ (M : M4 A) Y, T Y * M = T (Y * M.map π)) ∧ (∀ Y, adj (T Y) = T (adj Y)) ∧
      ∀ Y, IsUp Y → IsUp (T Y) := by
  let m : k →+ A := AddMonoidHom.mk' μ h1
  have h3 : ∀ (a : A) c, m (π a * c) = a * m c := h2
  refine ⟨m.mapMatrix, fun Y => rfl, fun M Y => ?_, fun M Y => ?_, fun Y => ?_, fun Y hY i j h => ?_⟩
  · ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, h3]
  · ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm (Y a c), h3, mul_comm]
  · ext a b
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, adj_apply, map_zsmul]
  · simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, hY i j h, map_zero]

private theorem isUp_mul {k : Type} [CommRing k] {X Y : M4 k} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c < i
  · rw [hX i c hc, zero_mul]
  · rw [hY c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]

private theorem isUp_add {k : Type} [CommRing k] {X Y : M4 k} (hX : IsUp X) (hY : IsUp Y) : IsUp (X + Y) := by
  intro i j h
  rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]

private theorem alg_id {S : Type} [Ring S] (a n B g y : S) (h : n * a = 1) :
    a * (B * g - (g * y - y * g)) * n + (a * (g * (y * n)) + a * -y * g * n) = a * B * n * (a * g * n) := by
  have : a * B * n * (a * g * n) = a * B * (n * a) * g * n := by simp only [mul_assoc]
  rw [this, h]
  noncomm_ring

private theorem rb_lc {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {Γ : Type} [TopologicalSpace Γ]
    {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (r : Γ → M4 R) (rb : Γ → M4 (ResidueField Λ))
    (hc : ∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) (hr : ∀ g, (r g).map (res Λ R) = rb g) :
    IsLocallyConstant rb := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have : ∀ a b, ∀ᶠ t in nhds s, rb t a b = rb s a b := fun a b => by
    filter_upwards [(hc a b 1).eventually_eq s] with t ht
    rw [Ideal.Quotient.eq, pow_one, ← res_eq_zero_iff Λ, map_sub, sub_eq_zero] at ht
    rw [← hr, ← hr]
    exact ht
  filter_upwards [Filter.eventually_all.2 fun a => Filter.eventually_all.2 (this a)] with t ht
  ext a b
  exact ht a b

theorem UpperTheory.V.Ws.X1.obCor :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∀ (rb : Γ →* M4 (ResidueField Λ)) (nb : V → M4 (ResidueField Λ)) (hb : ∀ g, ∃ x, IsGSp x (rb g)), (∀ g, (r g).map (res Λ R) = rb g) → (∀ v, (n v).map (res Λ R) = nb v) → ∀ (D : SL loc ν r n p) (μ : ResidueField Λ → A), (∀ c d, μ (c + d) = μ c + μ d) → (∀ (a : A) c, μ (res Λ A a * c) = a * μ c) → (∀ c, p (μ c) = 0) → ∀ x ∈ Fr.continuousCoboundaries2 loc (adSp rb hb) (fun v => bor (nb v)), (∀ s t, D.om s t = ((x.1 (s, t)).1 * rb (s * t)).map μ) → (∀ v s, D.de v s = ((x.2 v s).1 * rb (loc v s)).map μ) → WLift loc ν r n p := by
  intro Λ _ _ _ _ Γ V _ _ _ Gv _ _ _ loc hloc A R _ _ _ _ _ _ p hp hs ν r n hν hW hc rb nb hb hr hn D μ m1 m2 m3
    x hx x1 x2
  obtain ⟨T, T0, Tl, Tr, Ta, Tu⟩ := exists_strictHenselian_absolutely_closed_local_ring (res Λ A) μ m1 m2
  simp only [T0, SL.om, SL.de] at x1 x2
  have lc := rb_lc r rb hc hr
  obtain ⟨h, y, b1, b3, b4⟩ := hx
  obtain ⟨class_group_mod_eq_torsion, -, gA3, -, -, gA6, -⟩ := grp A
  obtain ⟨gR1, -, -, -, -, gR6, -⟩ := grp R
  obtain ⟨gk1, -⟩ := grp (ResidueField Λ)
  have aA : ∀ X : M4 A, (adj X).map (res Λ A) = adj (X.map (res Λ A)) := fun X =>
    (gA6 _ (res Λ A : A →+* ResidueField Λ) X).symm
  have aR : ∀ X : M4 R, (adj X).map (res Λ R) = adj (X.map (res Λ R)) := fun X =>
    (gR6 _ (res Λ R : R →+* ResidueField Λ) X).symm
  have mR : ∀ X Y : M4 R, (X * Y).map (res Λ R) = X.map (res Λ R) * Y.map (res Λ R) := fun X Y =>
    Matrix.map_mul (f := (res Λ R : R →+* ResidueField Λ))
  have Tp : ∀ Y, (T Y).map p = 0 := fun Y => by
    rw [← T0]; ext a b; exact m3 _
  have Tres : ∀ Y, (T Y).map (res Λ A) = 0 := fun Y => by
    rw [← T0]; ext a b
    show res Λ A (μ _) = 0
    rw [← UpperTheory.V.Alg.res_map p, m3, map_zero]
  have TT : ∀ Y Y', T Y * T Y' = 0 := fun Y Y' => by rw [Tl, Tres, zero_mul, map_zero]
  have rtres : ∀ s, (D.rt s).map (res Λ A) = rb s := fun s => by
    ext a b
    rw [Matrix.map_apply, ← UpperTheory.V.Alg.res_map p, ← hr, ← D.rt_map, Matrix.map_apply, Matrix.map_apply]
  have ntres : ∀ v, (D.nt v).map (res Λ A) = nb v := fun s => by
    ext a b
    rw [Matrix.map_apply, ← UpperTheory.V.Alg.res_map p, ← hn, ← D.nt_map, Matrix.map_apply, Matrix.map_apply]
  have pert : ∀ (c : A) (g : M4 A) (Y : M4 (ResidueField Λ)), IsGSp c g → Y ∈ sp4 (ResidueField Λ) →
      IsGSp c (g + T (Y * g.map (res Λ A))) := fun c g Y hg hY => by
    have hY' : adj Y = -Y := hY
    unfold IsGSp at *
    rw [gA3, Ta, gk1, hY', add_mul, mul_add, mul_add, TT, Tl, Tr, hg, aA]
    simp only [mul_neg, neg_mul, map_neg, mul_assoc]
    abel
  have inv1 : ∀ s, rb s * rb s⁻¹ = 1 := fun s => by rw [← map_mul, mul_inv_cancel, map_one]
  have inv2 : ∀ s, rb s⁻¹ * rb s = 1 := fun s => by rw [← map_mul, inv_mul_cancel, map_one]
  set f : Γ → M4 A := fun s => D.rt s - T ((h s).1 * rb s) with hf
  have fH : ∀ s, IsGSp (algebraMap Λ A (ν s)) (f s) := fun s => by
    have := pert _ _ _ (D.rt_mult s) (-h s).2
    rw [rtres, Submodule.coe_neg, neg_mul, map_neg, ← sub_eq_add_neg] at this
    exact this
  have fmul : ∀ s t, f (s * t) = f s * f t := fun s t => by
    have e := x1 s t
    rw [b3, sub_eq_iff_eq_add] at e
    have e' : ((dOne (adSp rb hb) h (s, t)).1 : M4 _) * rb (s * t) =
        (h s).1 * rb s * rb t + rb s * ((h t).1 * rb t) - (h (s * t)).1 * rb (s * t) := by
      show ((h s).1 + rb s * (h t).1 * rb s⁻¹ - (h (s * t)).1) * rb (s * t) = _
      rw [sub_mul, add_mul, map_mul, mul_assoc (rb s * (h t).1), ← mul_assoc (rb s⁻¹), inv2, one_mul]
      simp only [mul_assoc]
    rw [hf]
    simp only
    rw [sub_mul, mul_sub, mul_sub, TT, Tl, Tr, rtres, rtres, e, e', map_sub, map_add (f := _)]
    abel
  have fone : f 1 = 1 := by
    have hu : adj (f 1) * f 1 = 1 := by
      have := fH 1
      unfold IsGSp at this
      rw [this]; simp
    have := fmul 1 1
    rw [mul_one] at this
    calc f 1 = adj (f 1) * f 1 * f 1 := by rw [hu, one_mul]
      _ = 1 := by rw [mul_assoc, ← this, hu]
  have fp : ∀ s, (f s).map p = r s := fun s => by
    rw [hf]
    simp only
    rw [Matrix.map_sub _ (map_sub p), Tp, D.rt_map, sub_zero]
  have fres : ∀ s, (f s).map (res Λ A) = rb s := fun s => by
    ext a b
    rw [Matrix.map_apply, ← UpperTheory.V.Alg.res_map p, ← hr, ← fp, Matrix.map_apply, Matrix.map_apply]
  refine ⟨{ toFun := f, map_one' := fone, map_mul' := fmul }, fun v => D.nt v + T ((y v).1 * nb v),
    ⟨fH, fun v => ?_, fun v s => ?_⟩, fun a b N => ?_, fp, fun v => ?_⟩
  · have := pert _ _ _ (D.nt_sp v) (y v).2
    rwa [ntres] at this
  · have n1 : adj (D.nt v) * D.nt v = 1 := by
      have := D.nt_sp v
      unfold IsGSp at this
      rw [this, one_smul]
    have n2 : adj (nb v) * nb v = 1 := by
      rw [← ntres, ← aA]
      have := congrArg (fun X : M4 A => X.map (res Λ A : A →+* ResidueField Λ)) n1
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    have n3 : nb v * adj (nb v) = 1 := mul_eq_one_comm.1 n2
    have u1 : IsUp (adj (nb v) * rb (loc v s) * nb v) := fun i j hij => by
      rw [← hn, ← hr, ← aR, ← mR, ← mR, Matrix.map_apply, hW.flag v s i j hij, map_zero]
    have u2 : IsUp (adj (nb v) * ((x.2 v s).1 - ((h (loc v s)).1 - (rb (loc v s) * (y v).1 * rb (loc v s)⁻¹ - (y v).1)))
      * nb v) := b4 v s
    set B := (x.2 v s).1 - ((h (loc v s)).1 - (rb (loc v s) * (y v).1 * rb (loc v s)⁻¹ - (y v).1)) with hB
    have e := x2 v s
    rw [sub_eq_iff_eq_add] at e
    have hy : adj (y v).1 = -(y v).1 := (y v).2
    have e1 : f (loc v s) = D.nt v * D.t v s * adj (D.nt v) +
        T (B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s))) := by
      have : B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s)) =
          (x.2 v s).1 * rb (loc v s) - (h (loc v s)).1 * rb (loc v s) := by
        rw [hB, sub_mul, sub_mul, sub_mul, mul_assoc _ _ (rb (loc v s)), inv2, mul_one]
        abel
      rw [this, map_sub, hf]
      simp only
      rw [e]
      abel
    have e2 : adj (D.nt v) * f (loc v s) * D.nt v = D.t v s +
        T (adj (nb v) * (B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s))) * nb v) := by
      rw [e1, mul_add, add_mul, Tl, Tr, aA, ntres]
      congr 1
      rw [← mul_assoc, ← mul_assoc, n1, one_mul, mul_assoc, n1, mul_one]
    have key : adj (D.nt v + T ((y v).1 * nb v)) * f (loc v s) * (D.nt v + T ((y v).1 * nb v)) =
        D.t v s + T ((adj (nb v) * B * nb v) * (adj (nb v) * rb (loc v s) * nb v)) := by
      rw [gA3, Ta, gk1, hy, add_mul, add_mul, mul_add, mul_add, e2, Tr (f _), TT, Tr (D.nt v),
        mul_assoc (adj (D.nt v)), Tl, Tl, fres, aA, ntres, add_zero, add_assoc, add_assoc, ← map_add, ← map_add]
      exact congrArg (fun Z => D.t v s + T Z) (alg_id _ _ _ _ _ n3)
    show IsUp (adj (D.nt v + T ((y v).1 * nb v)) * f (loc v s) * (D.nt v + T ((y v).1 * nb v)))
    rw [key]
    exact isUp_add (D.t_up v s) (Tu _ (isUp_mul u2 u1))
  · have c1 := D.rt_cont a b N
    have c2 : IsLocallyConstant fun s => Ideal.Quotient.mk (maximalIdeal A ^ N) (T ((h s).1 * rb s) a b) :=
      ((b1.comp Subtype.val).mul lc).comp fun Y => Ideal.Quotient.mk (maximalIdeal A ^ N) (T Y a b)
    have c3 := c1.sub c2
    convert c3 using 2 with s
    exact map_sub _ _ _
  · show (D.nt v + T _).map p = _
    rw [Matrix.map_add _ (map_add p), Tp, add_zero, D.nt_map]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.LowLift
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

variable {A R : Type} [CommRing A] [CommRing R]

private def lowOf (a b c d : A) : M4 A := !![1, 0, 0, 0; a, 1, 0, 0; b, c, 1, 0; d, b - a * c, -a, 1]

private theorem lowOf_low (a b c d : A) : IsLow (lowOf a b c d) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsGSp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adj, lowOf, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, Matrix.one_apply] <;> ring
  · intro i
    fin_cases i <;> simp [lowOf]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [lowOf] <;> omega

private theorem eq_lowOf {n : M4 A} (h : IsLow n) : n = lowOf (n 1 0) (n 2 0) (n 2 1) (n 3 0) := by
  obtain ⟨hg, hd, hu⟩ := h
  have h01 := hu 0 1 (by decide); have h02 := hu 0 2 (by decide); have h03 := hu 0 3 (by decide)
  have h12 := hu 1 2 (by decide); have h13 := hu 1 3 (by decide); have h23 := hu 2 3 (by decide)
  have d0 := hd 0; have d1 := hd 1; have d2 := hd 2; have d3 := hd 3
  have e1 := congrFun (congrFun hg 1) 0
  have e4 := congrFun (congrFun hg 3) 1
  simp [adj, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, Matrix.one_apply, h01, h02, h03, h12, h13,
    h23, d0, d1, d2, d3] at e1 e4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowOf, h01, h02, h03, h12, h13, h23, d0, d1, d2, d3]
  · linear_combination e4
  · linear_combination e1

private theorem low_mul {m n : M4 A} (hm : IsLow m) (hn : IsLow n) : IsLow (m * n) := by
  refine ⟨by simpa using (grp A).2.2.2.2.2.2.2.1 1 1 m n hm.1 hn.1, ?_, ?_⟩
  · intro i
    rw [eq_lowOf hm, eq_lowOf hn]
    fin_cases i <;> simp [lowOf, Matrix.mul_apply, Fin.sum_univ_four]
  · intro i j hij
    rw [eq_lowOf hm, eq_lowOf hn]
    fin_cases i <;> fin_cases j <;> simp_all [lowOf, Matrix.mul_apply, Fin.sum_univ_four] <;> omega

private theorem up_adj {b : M4 A} (h : IsUp b) : IsUp (adj b) := by
  intro i j hij
  rw [adj_apply, h j.rev i.rev (by simpa [Fin.lt_def, Fin.val_rev] using (by omega : (3 : ℕ) - i.val < 3 - j.val)), smul_zero]

private theorem aux (p : A →+* R) (hp : ∀ x y, p x = 0 → p y = 0 → x * y = 0) (n' : M4 A) (hn : IsGSp 1 n')
    (hl : IsLow (n'.map p)) :
    ∃ m b : M4 A, IsLow m ∧ IsGSp 1 b ∧ IsUp b ∧ IsUp (adj b) ∧ m.map p = n'.map p ∧ m = n' * b := by
  obtain ⟨-, -, hadd, hsmul, hone, hmap, -, hgsp, -⟩ := grp A
  have kz : ∀ X Z : M4 A, X.map p = 0 → Z.map p = 0 → X * Z = 0 := by
    intro X Z hX hZ
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ =>
      hp _ _ (by simpa using congrFun (congrFun hX i) k) (by simpa using congrFun (congrFun hZ k) j)
  have adj0 : adj (0 : M4 A) = 0 := by simpa using hsmul 0 (0 : M4 A)
  have adjneg : ∀ X : M4 A, adj (-X) = -adj X := by
    intro X
    simpa using hsmul (-1) X
  have madj : ∀ X : M4 A, X.map p = 0 → (adj X).map p = 0 := by
    intro X hX
    rw [← hmap R p X, hX]
    simpa using (grp R).2.2.2.1 (0 : R) (0 : M4 R)
  set m0 := lowOf (n' 1 0) (n' 2 0) (n' 2 1) (n' 3 0) with hm0d
  have hm0 : IsLow m0 := lowOf_low _ _ _ _
  have hm0l : adj m0 * m0 = 1 := by simpa [IsGSp] using hm0.1
  have hm0r : m0 * adj m0 = 1 := mul_eq_one_comm.mp hm0l
  have hmap0 : m0.map p = n'.map p := by
    rw [eq_lowOf hl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hm0d, lowOf]
  have hN : adj (n'.map p) * n'.map p = 1 := by simpa [IsGSp] using hl.1
  set Y := adj m0 * n' - 1 with hYd
  have hY : Y.map p = 0 := by
    show p.mapMatrix Y = 0
    rw [hYd, map_sub, map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← hmap R p m0,
      hmap0, hN, sub_self]
  have h1Y : adj m0 * n' = 1 + Y := by rw [hYd]; abel
  have ha : IsGSp 1 (adj m0) := by
    show adj (adj m0) * adj m0 = (1 : A) • 1
    rw [(grp A).2.1, hm0r, one_smul]
  have hadjY : adj Y + Y = 0 := by
    have g : IsGSp 1 (adj m0 * n') := by simpa using hgsp 1 1 _ _ ha hn
    have g' : adj (1 + Y) * (1 + Y) = 1 := by simpa [IsGSp, h1Y] using g
    rw [hadd, hone] at g'
    have e : (1 + adj Y) * (1 + Y) = 1 + (adj Y + Y) + adj Y * Y := by noncomm_ring
    rw [e, kz _ _ (madj Y hY) hY, add_zero] at g'
    simpa using g'
  set Yu : M4 A := Matrix.of fun i j => if i ≤ j then Y i j else 0 with hYud
  have hYu : Yu.map p = 0 := by
    ext i j
    have := congrFun (congrFun hY i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    simp only [hYud, Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply]
    split_ifs <;> simp [this]
  have hadjYu : adj Yu + Yu = 0 := by
    ext i j
    have h := congrFun (congrFun hadjY i) j
    simp only [Matrix.add_apply, adj_apply, Matrix.zero_apply] at h
    simp only [Matrix.add_apply, adj_apply, Matrix.zero_apply, hYud, Matrix.of_apply, Fin.rev_le_rev]
    split_ifs <;> simp_all
  set b : M4 A := 1 - Yu with hbd
  have hbup : IsUp b := by
    intro i j hij
    simp [hbd, hYud, Matrix.one_apply, hij.ne', not_le.mpr hij]
  have hbg : IsGSp 1 b := by
    show adj b * b = (1 : A) • 1
    have ea : adj b = 1 - adj Yu := by
      rw [hbd, sub_eq_add_neg, hadd, adjneg, hone, ← sub_eq_add_neg]
    rw [ea, one_smul]
    have e : (1 - adj Yu) * (1 - Yu) = 1 - (adj Yu + Yu) + adj Yu * Yu := by noncomm_ring
    rw [e, hadjYu, kz _ _ (madj Yu hYu) hYu]
    simp
  have hbmap : p.mapMatrix b = 1 := by
    rw [hbd, map_sub, map_one, RingHom.mapMatrix_apply, hYu, sub_zero]
  have e1 : adj m0 * n' * b = 1 + (Y - Yu) := by
    rw [h1Y, hbd]
    have e : (1 + Y) * (1 - Yu) = 1 + (Y - Yu) - Y * Yu := by noncomm_ring
    rw [e, kz _ _ hY hYu, sub_zero]
  have hlow : IsLow (adj m0 * n' * b) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa using hgsp _ _ _ _ (by simpa using hgsp 1 1 _ _ ha hn) hbg
    · intro i
      rw [e1]
      simp [hYud]
    · intro i j hij
      rw [e1]
      simp [hYud, Matrix.one_apply, hij.ne, hij.le]
  have hm := low_mul hm0 hlow
  have hmeq : m0 * (adj m0 * n' * b) = n' * b := by
    rw [← mul_assoc, ← mul_assoc, hm0r, one_mul]
  refine ⟨m0 * (adj m0 * n' * b), b, hm, hbg, hbup, up_adj hbup, ?_, hmeq⟩
  rw [hmeq]
  show p.mapMatrix (n' * b) = p.mapMatrix n'
  rw [map_mul, hbmap, mul_one]

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.lowLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ n' : M4 A, IsGSp 1 n' → IsLow (n'.map p) → ∃ m b : M4 A, IsLow m ∧ IsGSp 1 b ∧ IsUp b ∧ IsUp (adj b) ∧ m.map p = n'.map p ∧ m = n' * b := by
  intro Λ _ _ _ _ A R _ _ _ _ _ _ p _ hker n' hn hl
  have hle : RingHom.ker p ≤ maximalIdeal A := by
    apply IsLocalRing.le_maximalIdeal
    intro htop
    have h1 : (1 : A) ∈ RingHom.ker p := by rw [htop]; trivial
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  refine aux (p : A →+* R) (fun x y hx hy => ?_) n' hn hl
  have hm : x * y ∈ maximalIdeal A * RingHom.ker p :=
    Ideal.mul_mem_mul (hle (by simpa [RingHom.mem_ker] using hx)) (by simpa [RingHom.mem_ker] using hy)
  rw [hker] at hm
  simpa using hm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.RankAdjLe
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

private theorem rank_adj_le {k : Type} [Field k] (X : M4 k) : (adj X).rank ≤ X.rank := by
  have e : adj X = Matrix.diagonal (fun i => (sgn i : k)) * ((Matrix.transpose X).submatrix Fin.rev Fin.rev) * Matrix.diagonal (fun i => (sgn i : k)) := by
    ext i j
    rw [adj_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply, Matrix.transpose_apply, zsmul_eq_mul]
    push_cast
    ring
  rw [e]
  calc _ ≤ (Matrix.diagonal (fun i => (sgn i : k)) * ((Matrix.transpose X).submatrix Fin.rev Fin.rev)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ ((Matrix.transpose X).submatrix Fin.rev Fin.rev).rank := Matrix.rank_mul_le_right _ _
    _ = X.rank := by
      rw [← Matrix.rank_transpose X]
      exact Matrix.rank_submatrix (Matrix.transpose X) Fin.revPerm Fin.revPerm

private noncomputable def cmp {k : Type} [Field k] (p : M4 k) :
    M4 k →ₗ[k] (LinearMap.range p.mulVecLin →ₗ[k] LinearMap.range p.mulVecLin) where
  toFun X := p.mulVecLin.rangeRestrict ∘ₗ X.mulVecLin ∘ₗ (LinearMap.range p.mulVecLin).subtype
  map_add' X Y := by
    rw [Matrix.mulVecLin_add, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' a X := by
    ext v i
    simp [Matrix.smul_mulVec, Matrix.mulVec_smul]

private theorem cmp_zero {k : Type} [Field k] (p X : M4 k) (h : cmp p X = 0) : p * X * p = 0 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun w => ?_
  simp only [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h2 := congrArg Subtype.val (LinearMap.congr_fun h ⟨Matrix.mulVec p w, w, rfl⟩)
  simpa [cmp] using h2

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.ccDim :
    ∀ {k Γ : Type} [Field k] [Group Γ] (r : Γ →* M4 k) (h : ∀ g, ∃ x, IsGSp x (r g)), (2 : k) ≠ 0 → ∀ s : Γ, s * s = 1 → IsGSp (-1) (r s) → Module.finrank k (LinearMap.ker (adSp r h s - 1)) ≤ 4 := by
  intro k Γ _ _ r h h2 s hss hs
  set g := r s with hgdef
  have adj_mul := (grp k).1
  have adj_adj := (grp k).2.1
  have adj_add := (grp k).2.2.1
  have adj_smul := (grp k).2.2.2.1
  have adj_one := (grp k).2.2.2.2.1
  have hg2 : g * g = 1 := by rw [hgdef, ← r.map_mul, hss, r.map_one]
  have hsi : s⁻¹ = s := (eq_inv_of_mul_eq_one_left hss).symm
  have hadj : adj g = -g := by
    have e : adj g * g = (-1 : k) • 1 := hs
    calc adj g = adj g * g * g := by rw [Matrix.mul_assoc, hg2, Matrix.mul_one]
      _ = -g := by rw [e]; simp
  set c : k := (2 : k)⁻¹ with hc
  have hc2 : c * 2 = 1 := inv_mul_cancel₀ h2
  set p : M4 k := c • (1 + g) with hp
  set q : M4 k := c • (1 - g) with hq
  have hpq : p + q = 1 := by
    rw [hp, hq, ← smul_add]
    have e : (1 + g) + (1 - g) = (2 : k) • (1 : M4 k) := by rw [two_smul]; abel
    rw [e, smul_smul, hc2, one_smul]
  have hadjp : adj p = q := by
    rw [hp, hq, adj_smul, adj_add, adj_one, hadj, sub_eq_add_neg]
  have hadjq : adj q = p := by rw [← hadjp, adj_adj]
  have hpq0 : p * q = 0 := by
    have e : (1 + g) * (1 - g) = 0 := by
      rw [add_mul, mul_sub, mul_sub, hg2]
      simp
    rw [hp, hq, smul_mul_assoc, mul_smul_comm, e]
    simp
  have hpp : p * p = p := by
    have e : p * p = p * (p + q) := by rw [mul_add, hpq0, add_zero]
    rw [e, hpq, mul_one]
  have hrk : p.rank ≤ 2 := by
    have h1 : q.rank ≤ p.rank := by rw [← hadjp]; exact rank_adj_le p
    have h1' : p.rank ≤ q.rank := by rw [← hadjq]; exact rank_adj_le q
    have hle : LinearMap.range q.mulVecLin ≤ LinearMap.ker p.mulVecLin := by
      rintro _ ⟨w, rfl⟩
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hpq0, Matrix.zero_mulVec]
    have hmono := Submodule.finrank_mono hle
    have hsum := LinearMap.finrank_range_add_finrank_ker p.mulVecLin
    rw [Module.finrank_fin_fun] at hsum
    have eq1 : q.rank = Module.finrank k (LinearMap.range q.mulVecLin) := rfl
    have eq2 : p.rank = Module.finrank k (LinearMap.range p.mulVecLin) := rfl
    omega
  let K := LinearMap.ker (adSp r h s - 1)
  let ψ : K →ₗ[k] (LinearMap.range p.mulVecLin →ₗ[k] LinearMap.range p.mulVecLin) :=
    cmp p ∘ₗ (sp4 k).subtype ∘ₗ K.subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨Y, hYsp⟩, hYk⟩ hY
    have hYa : adj Y = -Y := hYsp
    have hfix : g * Y * g = Y := by
      have e := LinearMap.mem_ker.mp hYk
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at e
      have e2 := congrArg Subtype.val e
      rw [adSp_val, hsi] at e2
      exact e2
    have hcomm : g * Y = Y * g := by
      calc g * Y = g * Y * (g * g) := by rw [hg2, Matrix.mul_one]
        _ = (g * Y * g) * g := by simp only [Matrix.mul_assoc]
        _ = Y * g := by rw [hfix]
    have hpY : p * Y = Y * p := by
      rw [hp, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hcomm]
    have hz : p * Y * p = 0 := cmp_zero p Y hY
    have hYp : Y * p = 0 := by
      rw [hpY, Matrix.mul_assoc, hpp] at hz
      exact hz
    have h0 : adj (0 : M4 k) = 0 := by simpa using adj_smul 0 0
    have hqY : q * Y = 0 := by
      have e := congrArg adj hYp
      rw [adj_mul, hadjp, hYa, h0, Matrix.mul_neg, neg_eq_zero] at e
      exact e
    have hq' : q = 1 - p := eq_sub_of_add_eq' hpq
    have hYq : Y * q = 0 := by
      rw [hq'] at hqY ⊢
      rw [Matrix.mul_sub, Matrix.mul_one, ← hpY]
      rw [Matrix.sub_mul, Matrix.one_mul] at hqY
      exact hqY
    have hY0 : Y = 0 := by
      calc Y = Y * (p + q) := by rw [hpq, Matrix.mul_one]
        _ = 0 := by rw [Matrix.mul_add, hYp, hYq, add_zero]
    apply Subtype.ext
    apply Subtype.ext
    exact hY0
  calc Module.finrank k K ≤ Module.finrank k (LinearMap.range p.mulVecLin →ₗ[k] LinearMap.range p.mulVecLin) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = p.rank * p.rank := by rw [Module.finrank_linearMap]; rfl
    _ ≤ 2 * 2 := Nat.mul_le_mul hrk hrk
    _ = 4 := rfl
end

