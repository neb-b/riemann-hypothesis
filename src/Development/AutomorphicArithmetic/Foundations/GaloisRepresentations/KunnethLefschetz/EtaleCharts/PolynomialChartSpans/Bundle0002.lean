module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BCoord
section
open CategoryTheory Limits MvPolynomial

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem etale_chart {A E B : Type} [CommRing A] [CommRing E] [CommRing B] {D : ℕ}
    (p : A →+* E) (ψ : E →+* B) (s : Fin D → E) (y : Fin D → B) (j : Fin D)
    (hφ : (eval₂Hom p s).Etale)
    (surj : Function.Surjective (eval₂Hom ψ y))
    (ker : RingHom.ker (eval₂Hom ψ y) = Ideal.span (insert (X j - 1 : MvPolynomial (Fin D) E)
      (Set.range fun k => MvPolynomial.C (s k) - MvPolynomial.C (s j) * X k))) :
    (eval₂Hom (ψ.comp p) (Function.update y j (ψ (s j)))).Etale := by
  classical
  let γ := eval₂Hom (ψ.comp p) (Function.update y j (ψ (s j)))
  let Z : Fin D → MvPolynomial (Fin D) A := Function.update X j 1
  let α' : MvPolynomial (ULift.{0} (Fin D)) A →+* E := eval₂Hom p (fun k => s k.down)
  let β' : MvPolynomial (ULift.{0} (Fin D)) A →+* MvPolynomial (Fin D) A :=
    eval₂Hom C (fun k => X j * Z k.down)
  have hα' : α'.Etale := by
    have e1 : α' = (eval₂Hom p s).comp
        (MvPolynomial.renameEquiv A Equiv.ulift).toRingEquiv.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [α']
      · intro k
        simp [α']
    rw [e1]
    exact RingHom.Etale.respectsIso.2 _ _ hφ
  have hker : ∀ q ∈ Ideal.span (insert (X j - 1 : MvPolynomial (Fin D) E)
      (Set.range fun k => C (s k) - C (s j) * X k)), eval₂Hom ψ y q = 0 := by
    intro q hq
    rw [← ker] at hq
    exact hq
  have hyj : y j = 1 := by
    have h0 := hker _ (Ideal.subset_span (Set.mem_insert _ _))
    simp only [map_sub, eval₂Hom_X', map_one] at h0
    exact sub_eq_zero.1 h0
  have hyk : ∀ k, ψ (s k) = ψ (s j) * y k := by
    intro k
    have h0 := hker _ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩))
    simp only [map_sub, map_mul, eval₂Hom_C, eval₂Hom_X'] at h0
    exact sub_eq_zero.1 h0
  have hγX : ∀ k, k ≠ j → γ (X k) = y k := by
    intro k hk
    simp [γ, Function.update_of_ne hk]
  have hγXj : γ (X j) = ψ (s j) := by simp [γ]
  have hγZ : ∀ k, γ (X j * Z k) = ψ (s k) := by
    intro k
    by_cases hk : k = j
    · subst hk
      simp [Z, hγXj]
    · rw [map_mul, hγXj]
      simp only [Z, Function.update_of_ne hk]
      rw [hγX k hk, hyk k]
  have hcompat : ∀ t, ψ (α' t) = γ (β' t) := by
    intro t
    have h0 : ψ.comp α' = γ.comp β' := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [α', β', γ]
      · intro k
        simp only [RingHom.comp_apply, α', β', eval₂Hom_X']
        exact (hγZ k.down).symm
    exact RingHom.congr_fun h0 t
  letI : Algebra (MvPolynomial (ULift.{0} (Fin D)) A) E := α'.toAlgebra
  letI : Algebra (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) := β'.toAlgebra
  letI : Algebra (MvPolynomial (ULift.{0} (Fin D)) A) B := (γ.comp β').toAlgebra
  have hbc := RingHom.Etale.isStableUnderBaseChange.tensorProduct (MvPolynomial (Fin D) A)
    (R := MvPolynomial (ULift.{0} (Fin D)) A) (S := E) hα'
  let fA : MvPolynomial (Fin D) A →ₐ[MvPolynomial (ULift.{0} (Fin D)) A] B :=
    { γ with commutes' := fun _ => rfl }
  let gA : E →ₐ[MvPolynomial (ULift.{0} (Fin D)) A] B :=
    { ψ with commutes' := fun t => hcompat t }
  let F := (Algebra.TensorProduct.lift fA gA (fun _ _ => Commute.all _ _)).toRingHom
  have hF : ∀ a e, F (TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) a e) = γ a * ψ e := by
    intro a e
    simp [F, fA, gA]
  have hT : ∀ t, TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) (α' t) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (β' t) (1 : E) := by
    intro t
    have h1 : α' t = t • (1 : E) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    have h2 : β' t = t • (1 : MvPolynomial (Fin D) A) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [h1, h2, TensorProduct.smul_tmul]
  have hTs : ∀ k, TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) (s k) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (X j * Z k) (1 : E) := by
    intro k
    simpa [α', β'] using hT (X ⟨k⟩)
  let G0 : MvPolynomial (Fin D) E →+* TensorProduct (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) E :=
    eval₂Hom (Algebra.TensorProduct.includeRight :
      E →ₐ[MvPolynomial (ULift.{0} (Fin D)) A] TensorProduct (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) E).toRingHom (fun k => TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (1 : E))
  have hG0C : ∀ e, G0 (C e) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) e := by
    intro e
    simp [G0]
  have hG0X : ∀ k, G0 (X k) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (1 : E) := by
    intro k
    simp [G0]
  have hG0 : RingHom.ker (eval₂Hom ψ y) ≤ RingHom.ker G0 := by
    rw [ker, Ideal.span_le]
    rintro q (rfl | ⟨k, rfl⟩)
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hG0X]
      simp [Z, Algebra.TensorProduct.one_def]
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, hG0C, hG0C, hG0X,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hTs k]
      have h3 : TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (s j) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (1 : E) * TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) (s j) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h3, hTs j, Algebra.TensorProduct.tmul_mul_tmul]
      simp [Z, mul_comm]
  let G : B →+* TensorProduct (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) E :=
    (Ideal.Quotient.lift _ G0 (fun q hq => hG0 hq)).comp
      (RingHom.quotientKerEquivOfSurjective surj).symm.toRingHom
  have hG : ∀ q, G (eval₂Hom ψ y q) = G0 q := by
    intro q
    have h4 : (RingHom.quotientKerEquivOfSurjective surj).symm (eval₂Hom ψ y q)
        = Ideal.Quotient.mk _ q := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.lift _ G0 (fun q hq => hG0 hq)
      ((RingHom.quotientKerEquivOfSurjective surj).symm (eval₂Hom ψ y q)) = G0 q
    rw [h4]
    rfl
  have hGψ : ∀ e, G (ψ e) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) e := by
    intro e
    rw [← eval₂Hom_C ψ y e, hG, hG0C]
  have hFG : F.comp G = RingHom.id B := by
    have h5 : F.comp G0 = eval₂Hom ψ y := by
      apply MvPolynomial.ringHom_ext
      · intro e
        rw [RingHom.comp_apply, hG0C, hF, map_one, one_mul, eval₂Hom_C]
      · intro k
        rw [RingHom.comp_apply, hG0X, hF, map_one, mul_one, eval₂Hom_X']
        by_cases hk : k = j
        · subst hk
          simp [Z, hyj]
        · simp only [Z, Function.update_of_ne hk]
          exact hγX k hk
    apply RingHom.ext
    intro b
    obtain ⟨q, rfl⟩ := surj b
    rw [RingHom.comp_apply, hG, RingHom.id_apply]
    exact RingHom.congr_fun h5 q
  have hGγ : ∀ a, G (γ a) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) a (1 : E) := by
    have h6 : G.comp γ = Algebra.TensorProduct.includeLeftRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        have h7 := hT (C c)
        simp only [α', β', eval₂Hom_C] at h7
        simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
        simp only [γ, eval₂Hom_C, RingHom.comp_apply]
        rw [hGψ, h7]
      · intro k
        simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
        by_cases hk : k = j
        · subst hk
          rw [hγXj, hGψ, hTs]
          simp [Z]
        · rw [hγX k hk, ← eval₂Hom_X' ψ y k, hG, hG0X]
          simp only [Z, Function.update_of_ne hk]
    intro a
    exact RingHom.congr_fun h6 a
  have hGF : G.comp F = RingHom.id _ := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [RingHom.comp_apply, hF, map_mul, RingHom.id_apply, hGγ, hGψ,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy =>
      simp only [RingHom.comp_apply, RingHom.id_apply, map_add (f := _)] at hx hy ⊢
      rw [hx, hy]
  let e := RingEquiv.ofRingHom F G hFG hGF
  have h8 := RingHom.Etale.respectsIso.1 _ e hbc
  convert h8 using 1
  apply RingHom.ext
  intro x
  show γ x = F (algebraMap _ _ x)
  rw [Algebra.TensorProduct.algebraMap_apply, hF, map_one, mul_one]
  rfl

end UpperTheory.Gal.KunnethLefschetz.G

open UpperTheory.Gal.DifferentialFormSections in
theorem UpperTheory.Gal.KunnethLefschetz.G.bCoord :
    UpperTheory.Gal.KunnethLefschetz.G.BCoord := by
  intro R _ Z W π D c b j
  exact UpperTheory.Gal.KunnethLefschetz.G.etale_chart _ _ c.s (b.y j) j (dCoord R Z D c) (b.surj j) (b.ker j)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpChart2
section
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

theorem blChart : BlowUpChart₂ := by
  intro R _ Z W _ π hπ D c
  set φ := MvPolynomial.eval₂Hom (secMap (p1 Z) c.h1).toRingHom c.s with hφ
  have hs : (fun k => φ (MvPolynomial.X k)) = c.s := by
    funext k
    simp [hφ]
  have hflat : φ.Flat := by
    have he := dCoord R Z D c
    algebraize [φ]
    exact Algebra.Smooth.flat _ _
  haveI : QuasiCompact (Over.Hom.left (dg Z)) := by
    change QuasiCompact (pullback.diagonal (Over.hom Z))
    infer_instance
  have hI : (Scheme.Hom.ker (Over.Hom.left (dg Z))).ideal ⟨c.N, c.aff⟩
      = Ideal.span (Set.range fun k => φ (MvPolynomial.X k)) := by
    rw [Scheme.Hom.ker_apply, hs, Scheme.Hom.app_eq_appLE]
    exact c.ker
  have key := bChartEx R π _ hπ ⟨c.N, c.aff⟩ D (Sec Z c.U) φ hflat hI
  rw [hs] at key
  exact key

end UpperTheory.Gal.KunnethLefschetz.G
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ExistsUnit
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections
open FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh (inter inter_le inter_le_comp mem_inter_iff)

namespace UpperTheory.Gal.KunnethLefschetz.G

section
variable {Y : Scheme.{0}}

private abbrev rs {U V : Y.Opens} (h : V ≤ U) : Γ(Y, U) →+* Γ(Y, V) := (Y.presheaf.map (homOfLE h).op).hom

private theorem rs_rs {U V T : Y.Opens} (h : V ≤ U) (h' : T ≤ V) (x : Γ(Y, U)) :
    rs h' (rs h x) = rs (h'.trans h) x := by
  change ((Y.presheaf.map (homOfLE h).op ≫ Y.presheaf.map (homOfLE h').op)).hom x = _
  rw [← Functor.map_comp]
  rfl

private theorem nzd_rs {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    {s : Γ(Y, U)} (hs : s ∈ nonZeroDivisors Γ(Y, U)) : rs h s ∈ nonZeroDivisors Γ(Y, V) := by
  have hf : (Scheme.Hom.appLE (𝟙 Y) U V h).hom.Flat :=
    HasRingHomProperty.appLE (P := @Flat) (Q := RingHom.Flat) (𝟙 Y) inferInstance ⟨U, hU⟩ ⟨V, hV⟩ h
  have e : (Scheme.Hom.appLE (𝟙 Y) U V h).hom = rs h := by
    ext x
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    rfl
  rw [e] at hf
  letI : Algebra Γ(Y, U) Γ(Y, V) := (rs h).toAlgebra
  haveI : Module.Flat Γ(Y, U) Γ(Y, V) := hf
  have hr : IsSMulRegular Γ(Y, U) s := fun a b e => (mul_cancel_left_mem_nonZeroDivisors hs).1 e
  have hr' := IsSMulRegular.of_flat (S := Γ(Y, V)) hr
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply hr'
  change rs h s * x = rs h s * 0
  rw [mul_zero, mul_comm]
  exact hx

private theorem exists_unit (J : Y.IdealSheafData) {U₁ U₂ T : Y.Opens}
    (a₁ : IsAffineOpen U₁) (a₂ : IsAffineOpen U₂) (aT : IsAffineOpen T) (h₁ : T ≤ U₁) (h₂ : T ≤ U₂)
    {s₁ : Γ(Y, U₁)} {s₂ : Γ(Y, U₂)} (e₁ : J.ideal ⟨U₁, a₁⟩ = Ideal.span {s₁})
    (e₂ : J.ideal ⟨U₂, a₂⟩ = Ideal.span {s₂})
    (n₂ : s₂ ∈ nonZeroDivisors Γ(Y, U₂)) :
    ∃ g : Γ(Y, T)ˣ, rs h₁ s₁ = g.val * rs h₂ s₂ := by
  have key : ∀ {U : Y.Opens} (a : IsAffineOpen U) (h : T ≤ U) {s : Γ(Y, U)},
      J.ideal ⟨U, a⟩ = Ideal.span {s} → J.ideal ⟨T, aT⟩ = Ideal.span {rs h s} := by
    intro U a h s e
    have := J.map_ideal (U := ⟨T, aT⟩) (V := ⟨U, a⟩) h
    rw [e, Ideal.map_span, Set.image_singleton] at this
    exact this.symm
  have k₁ := key a₁ h₁ e₁
  have k₂ := key a₂ h₂ e₂
  have m₁ : rs h₁ s₁ ∈ Ideal.span {rs h₂ s₂} := by
    rw [← k₂, k₁]; exact Ideal.mem_span_singleton_self _
  have m₂ : rs h₂ s₂ ∈ Ideal.span {rs h₁ s₁} := by
    rw [← k₁, k₂]; exact Ideal.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 m₁
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 m₂
  have n := nzd_rs a₂ aT h₂ n₂
  have hab : a * b = 1 := by
    refine (mul_cancel_left_mem_nonZeroDivisors n).1 ?_
    calc rs h₂ s₂ * (a * b) = b * (a * rs h₂ s₂) := by ring
      _ = rs h₂ s₂ * 1 := by rw [ha, hb, mul_one]
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

end

section
variable {K : Type} [CommRing K] {X : Sch K}

private theorem secRes_eq {U V : X.left.Opens} (h : V ≤ U) (x : Sec X U) :
    secRes X h x = rs h x := by
  change (Scheme.Hom.appLE (𝟙 X.left) U V h).hom x = _
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  rfl

private abbrev Idx (J : X.left.IdealSheafData) : Type :=
  Σ V : X.left.affineOpens, {s : Γ(X.left, V.1) // J.ideal V = Ideal.span {s} ∧ s ∈ nonZeroDivisors Γ(X.left, V.1)}

private abbrev idxU (J : X.left.IdealSheafData) (j : Idx J) : X.left.Opens := j.1.1

private theorem aff2 [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 2 → Idx J) :
    IsAffineOpen (cap (X := X) (idxU J) i) := by
  have : cap (X := X) (idxU J) i = idxU J (i 0) ⊓ idxU J (i 1) := by
    ext x
    simp [mem_inter_iff, Fin.forall_fin_two]
  rw [this]
  exact (i 0).1.2.inf (i 1).1.2

private theorem aff3 [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 3 → Idx J) :
    IsAffineOpen (cap (X := X) (idxU J) i) := by
  have : cap (X := X) (idxU J) i = idxU J (i 0) ⊓ idxU J (i 1) ⊓ idxU J (i 2) := by
    ext x
    simp [mem_inter_iff, Fin.forall_fin_succ, and_assoc]
  rw [this]
  exact ((i 0).1.2.inf (i 1).1.2).inf (i 2).1.2

private theorem exists_g [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 2 → Idx J) :
    ∃ g : Γ(X.left, cap (X := X) (idxU J) i)ˣ, rs (inter_le (X := X.left.toTopCat) (idxU J) i 0) (i 0).2.1 =
      g.val * rs (inter_le (X := X.left.toTopCat) (idxU J) i 1) (i 1).2.1 :=
  exists_unit J (i 0).1.2 (i 1).1.2 (aff2 J i) _ _ (i 0).2.2.1 (i 1).2.2.1 (i 1).2.2.2

private def gg [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 2 → Idx J) : Γ(X.left, cap (X := X) (idxU J) i)ˣ :=
  (exists_g (X := X) J i).choose

private theorem gg_spec [X.left.IsSeparated] (J : X.left.IdealSheafData) {T : X.left.Opens} (j : Fin 2 → Idx J)
    (a c : Idx J) (ha : j 0 = a) (hc : j 1 = c) (hT : T ≤ cap (X := X) (idxU J) j) (ta : T ≤ idxU J a) (tc : T ≤ idxU J c) :
    rs ta a.2.1 = rs hT (gg (X := X) J j).val * rs tc c.2.1 := by
  subst ha hc
  have e := congrArg (rs hT) (exists_g (X := X) J j).choose_spec
  rw [map_mul, rs_rs, rs_rs] at e
  exact e

private theorem gg_coc [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 3 → Idx J) :
    rs (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 2)) (gg (X := X) J (i ∘ Fin.succAbove 2)).val *
      rs (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 0)) (gg (X := X) J (i ∘ Fin.succAbove 0)).val =
      rs (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 1)) (gg (X := X) J (i ∘ Fin.succAbove 1)).val := by
  have t : ∀ a, cap (X := X) (idxU J) i ≤ idxU J (i a) := inter_le (X := X.left.toTopCat) (idxU J) i
  have A := gg_spec (X := X) J (i ∘ Fin.succAbove 2) (i 0) (i 1) rfl rfl
    (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 2)) (t 0) (t 1)
  have B := gg_spec (X := X) J (i ∘ Fin.succAbove 0) (i 1) (i 2) rfl rfl
    (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 0)) (t 1) (t 2)
  have C := gg_spec (X := X) J (i ∘ Fin.succAbove 1) (i 0) (i 2) rfl rfl
    (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 1)) (t 0) (t 2)
  refine (mul_cancel_right_mem_nonZeroDivisors (nzd_rs (i 2).1.2 (aff3 J i) (t 2) (i 2).2.2.2)).1 ?_
  rw [← C, mul_assoc, ← B, ← A]

private theorem exists_coc [X.left.IsSeparated] (J : X.left.IdealSheafData) (hJ : IsLocallyGeneratedByNonZeroDivisor J) :
    ∃ (L : Coc X) (s : ∀ j : L.ι, Sec X (L.U j)) (a : ∀ j, IsAffineOpen (L.U j)),
      (∀ j, J.ideal ⟨L.U j, a j⟩ = Ideal.span {(s j : Γ(X.left, L.U j))}) ∧
      (∀ j, s j ∈ nonZeroDivisors (Sec X (L.U j))) ∧
      ∀ j : Fin 2 → L.ι, secRes X (inter_le (X := X.left.toTopCat) L.U j 0) (s (j 0)) =
        (L.g j).val * secRes X (inter_le (X := X.left.toTopCat) L.U j 1) (s (j 1)) := by
  refine ⟨{ ι := Idx J, U := idxU J, cov := ⟨fun j => j.1.2, ?_⟩, g := gg (X := X) J, coc := ?_ }, fun j => j.2.1,
    fun j => j.1.2, fun j => j.2.2.1, fun j => j.2.2.2, fun j => ?_⟩
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨U, f, hx, hf, e⟩ := hJ x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, f, e, hf⟩, hx⟩
  · intro i
    simp only [secRes_eq]
    exact gg_coc (X := X) J i
  · refine (secRes_eq _ _).trans (((exists_g (X := X) J j).choose_spec).trans ?_)
    exact congrArg (fun t => (gg (X := X) J j).val * t) (secRes_eq _ _).symm

end

theorem exDiv : ExDiv := by
  intro R _ _ Z W D _ _ π hπ
  haveI : Smooth Z.hom := SmoothOfRelativeDimension.smooth D Z.hom
  obtain ⟨hp, hcl, -⟩ := blOff R π hπ
  haveI : IsProper π.left := hp
  haveI : IsClosedImmersion (dg Z).left := by
    change IsClosedImmersion (pullback.diagonal Z.hom)
    infer_instance
  haveI : IsSeparated (XX Z).hom := by
    change IsSeparated (pullback.fst Z.hom Z.hom ≫ Z.hom)
    infer_instance
  haveI : IsSeparated W.hom := by
    rw [← Over.w π]
    infer_instance
  haveI : W.left.IsSeparated := by
    constructor
    have : terminal.from W.left = W.hom ≫ terminal.from _ := terminal.hom_ext _ _
    rw [this]
    infer_instance
  obtain ⟨L, s, a, h1, h2, h3⟩ := exists_coc (X := W) _ hπ.1
  haveI : IsClosedImmersion (exI π).left := hcl
  refine ⟨L, s, hcl, fun j => ?_, h2, h3⟩
  have e : (exI π).left.ker = (dg Z).left.ker.comap π.left :=
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (dg Z).left π.left
  have e2 := Scheme.Hom.ker_apply (exI π).left ⟨L.U j, a j⟩
  rw [e, h1 j] at e2
  refine Eq.trans ?_ e2.symm
  change RingHom.ker (Scheme.Hom.appLE (exI π).left (L.U j) _ le_rfl).hom = _
  rw [Scheme.Hom.appLE_eq_app]

end UpperTheory.Gal.KunnethLefschetz.G
end
end

