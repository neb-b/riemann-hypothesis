module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExpEqOfPeriodsOfMarking

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLatForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem nsmul_canc {V : Type} [AddCommGroup V] [Module ℚ V] {a : ℕ} (ha : a ≠ 0) {x y : V}
    (h : a • x = a • y) : x = y := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have h' : (a : ℚ) • x = (a : ℚ) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]; exact h
  exact (smul_right_injective V ha') h'

private theorem ext_lin {Λ V V' : Type} [AddCommGroup Λ] [AddCommGroup V] [AddCommGroup V'] [Module ℚ V]
    [Module ℚ V'] (j : Λ →+ V) (hj : Function.Injective j)
    (hs : ∀ v, ∃ (m : ℕ) (u : Λ), m ≠ 0 ∧ m • v = j u) (f : Λ →+ V') :
    ∃ A : V →ₗ[ℚ] V', ∀ u, A (j u) = f u := by
  choose m u hm hu using hs
  let g : V → V' := fun v => ((m v : ℚ))⁻¹ • f (u v)
  have hg : ∀ v, m v • g v = f (u v) := by
    intro v
    have h0 : (m v : ℚ) ≠ 0 := by exact_mod_cast hm v
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ h0, one_smul]
  have key : ∀ (a : ℕ) (x : Λ) (v : V), a ≠ 0 → a • v = j x → a • g v = f x := by
    intro a x v ha hx
    have e : m v • x = a • u v := by
      apply hj
      rw [map_nsmul, map_nsmul, ← hx, ← hu v, smul_comm]
    apply nsmul_canc (hm v)
    rw [smul_comm, hg, ← map_nsmul, ← map_nsmul, e]
  have hadd : ∀ v₁ v₂, g (v₁ + v₂) = g v₁ + g v₂ := by
    intro v₁ v₂
    have h12 : m v₁ * m v₂ ≠ 0 := mul_ne_zero (hm _) (hm _)
    apply nsmul_canc h12
    rw [key (m v₁ * m v₂) (m v₂ • u v₁ + m v₁ • u v₂) (v₁ + v₂) h12 ?_]
    · rw [map_add (f := _), map_nsmul, map_nsmul, smul_add, ← hg v₁, ← hg v₂, smul_smul, smul_smul, mul_comm (m v₂),
        mul_comm (m v₁) (m v₂)]
    · rw [map_add (f := _), map_nsmul, map_nsmul, ← hu v₁, ← hu v₂, smul_add, smul_smul, smul_smul, mul_comm (m v₂)]
  refine ⟨(AddMonoidHom.mk' g hadd).toRatLinearMap, fun x => ?_⟩
  show g (j x) = f x
  have h1 : (1 : ℕ) • g (j x) = f x := key 1 x (j x) one_ne_zero (one_nsmul _)
  simpa using h1

theorem UpperTheory.Gal.W2.latForm_of :
    UpperTheory.Gal.W2.LatForm := by
  intro p _ D G L β β' D' D'' j j'' hP hP'' w m hm hw
  obtain ⟨hj, hjO, hjs, s₀, hs₀, hjF⟩ := hP
  obtain ⟨hj2, hjO2, hjs2, s₂, hs₂, hjF2⟩ := hP''
  obtain ⟨A, hA⟩ := ext_lin j'' hj2 hjs2 (j.comp w.toAddMonoidHom)
  replace hA : ∀ u, A (j'' u) = j (w u) := hA
  haveI := D.finLa
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hAinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun v hv => ?_
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    have h1 : j (w u) = 0 := by rw [← hA, ← hu, map_nsmul, hv, smul_zero]
    have h2 : w u = 0 := hj (by rw [h1, map_zero])
    have h3 : u = 0 := by
      refine D''.nondeg u fun u' => ?_
      have := hw u u'
      rw [h2] at this
      simp only [map_zero, LinearMap.zero_apply] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · exact absurd h hm.ne'
      · exact h
    apply nsmul_canc ha
    rw [hu, h3, map_zero, smul_zero]
  let Ae := LinearEquiv.ofInjectiveEndo A hAinj
  let B : Module.End ℚ (VQ D) := (Ae.symm : VQ D →ₗ[ℚ] VQ D)
  have hAB : A * B = 1 := LinearEquiv.ofInjectiveEndo_right_inv A hAinj
  have hBA : B * A = 1 := LinearEquiv.ofInjectiveEndo_left_inv A hAinj
  have hcomm : ∀ b, A * actQ D b = actQ D b * A := by
    intro b
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    apply nsmul_canc ha
    show a • A (actQ D b v) = a • actQ D b (A v)
    calc a • A (actQ D b v) = A (actQ D b (a • v)) := by rw [map_nsmul, map_nsmul]
      _ = A (j'' (b • u)) := by rw [hu, hjO2]
      _ = j (w (b • u)) := hA _
      _ = j (b • w u) := by rw [map_smul]
      _ = actQ D b (j (w u)) := hjO _ _
      _ = actQ D b (A (a • v)) := by rw [hu, hA]
      _ = a • actQ D b (A v) := by rw [map_nsmul, map_nsmul]
  have hBcomm : ∀ b, B * actQ D b = actQ D b * B := by
    intro b
    calc B * actQ D b = B * actQ D b * (A * B) := by rw [hAB, _root_.mul_one]
      _ = B * (actQ D b * A) * B := by simp only [_root_.mul_assoc]
      _ = B * (A * actQ D b) * B := by rw [hcomm]
      _ = (B * A) * actQ D b * B := by simp only [_root_.mul_assoc]
      _ = actQ D b * B := by rw [hBA, _root_.one_mul]
  obtain ⟨x, hx⟩ := (L.rep_range A).2 hcomm
  obtain ⟨x', hx'⟩ := (L.rep_range B).2 hBcomm
  have hxx' : x * x' = 1 := L.rep_inj (by rw [map_mul, hx, hx', hAB, map_one])
  have hx'x : x' * x = 1 := L.rep_inj (by rw [map_mul, hx, hx', hBA, map_one])
  let y : G.Cˣ := ⟨x, x', hxx', hx'x⟩
  have hform : ∀ v v', s₀ * D.EF.baseChange ℚ (L.rep ((β⁻¹ : G.Cˣ) : G.C) (A v)) (A v') =
      (m : ℚ) * s₂ * D.EF.baseChange ℚ (L.rep ((β'⁻¹ : G.Cˣ) : G.C) v) v' := by
    intro v v'
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    obtain ⟨b, u', hb, hu'⟩ := hjs2 v'
    have e1 := hjF (w u) (w u')
    have e2 := hjF2 u u'
    have e3 : ((D'.EF (w u) (w u') : ℤ) : ℚ) = (m : ℚ) * (D''.EF u u' : ℤ) := by
      rw [hw u u']; push_cast; ring
    unfold formB at e1 e2
    rw [← hA, ← hA, ← hu, ← hu', map_nsmul, map_nsmul, map_nsmul] at e1
    rw [← hu, ← hu', map_nsmul] at e2
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at e1 e2
    have hab : (a : ℚ) * b ≠ 0 := mul_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hb)
    apply mul_left_cancel₀ hab
    linear_combination -e1 + e3 + (m : ℚ) * e2
  have hnd : ∀ a : VQ D, (∀ v, D.EF.baseChange ℚ a v = 0) → a = 0 := by
    intro a ha
    obtain ⟨c, u, hc, hu⟩ := hjs (L.rep (β : G.C) a)
    have hinv : ∀ z : VQ D, L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (β : G.C) z) = z := by
      intro z
      rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
    have hu0 : u = 0 := by
      refine D'.nondeg u fun u' => ?_
      have e := hjF u u'
      unfold formB at e
      rw [← hu, map_nsmul, hinv] at e
      simp only [map_nsmul, LinearMap.smul_apply, ha, smul_zero, mul_zero] at e
      exact_mod_cast e
    have h0 : c • L.rep (β : G.C) a = c • (0 : VQ D) := by rw [hu, hu0, map_zero, smul_zero]
    have := nsmul_canc hc h0
    rw [← hinv a, this, map_zero]
  set r : ℚ := (m : ℚ) * s₂ / s₀ with hr
  have hr0 : 0 < r := by
    have : (0 : ℚ) < m := by exact_mod_cast hm
    positivity
  have hs₀' : s₀ ≠ 0 := hs₀.ne'
  have hshsh : sh G (sh G x) = x := G.star_star x
  have hkey : sh G x * ((β⁻¹ : G.Cˣ) : G.C) * x = algebraMap ℚ G.C r * ((β'⁻¹ : G.Cˣ) : G.C) := by
    apply L.rep_inj
    refine LinearMap.ext fun v => ?_
    rw [← sub_eq_zero]
    refine hnd _ fun v' => ?_
    have e := hform v v'
    have e2 := L.adj (sh G x) (L.rep ((β⁻¹ : G.Cˣ) : G.C) (A v)) v'
    rw [hshsh, hx] at e2
    simp only [map_mul, Module.End.mul_apply, hx, AlgHom.commutes, Module.algebraMap_end_apply,
      map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [e2, hr]
    field_simp
    linear_combination e
  refine ⟨y, Units.mk0 r hr0.ne', hr0, ?_, fun u => ?_⟩
  · show x * (β' : G.C) * sh G x = algebraMap ℚ G.C r * (β : G.C)
    have h1 : x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x) = r • x := by
      calc x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x)
          = x * (β' : G.C) * (sh G x * ((β⁻¹ : G.Cˣ) : G.C) * x) := by simp only [_root_.mul_assoc]
        _ = r • (x * ((β' : G.C) * ((β'⁻¹ : G.Cˣ) : G.C))) := by
            rw [hkey, ← Algebra.smul_def, mul_smul_comm, _root_.mul_assoc]
        _ = r • x := by rw [Units.mul_inv, _root_.mul_one]
    calc x * (β' : G.C) * sh G x
        = x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * (x * x') * (β : G.C)) := by
          rw [hxx', _root_.mul_one, Units.inv_mul, _root_.mul_one]
      _ = x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x) * (x' * (β : G.C)) := by
          simp only [_root_.mul_assoc]
      _ = r • (x * x' * (β : G.C)) := by rw [h1, smul_mul_assoc, _root_.mul_assoc]
      _ = algebraMap ℚ G.C r * (β : G.C) := by rw [hxx', _root_.one_mul, Algebra.smul_def]
  · show j (w u) = L.rep x (j'' u)
    rw [hx, hA]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLatIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.LatticeIsomorphism

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

private theorem rd_add (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (u v : VQ D) :
    rd L x h (u + v) = rd L x h u + rd L x h v := by
  simp only [rd, TensorProduct.tmul_add, map_add (f := _)]

private noncomputable def rdHom (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) : VQ D →+ AfP p ⊗[ℚ] VQ D :=
  AddMonoidHom.mk' (rd L x h) (rd_add L x h)

private theorem rd_sub (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (u v : VQ D) :
    rd L x h (u - v) = rd L x h u - rd L x h v := by
  exact map_sub (rdHom L x h) u v

private theorem rd_nsmul (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (n : ℕ) (u : VQ D) :
    rd L x h (n • u) = n • rd L x h u := by
  exact map_nsmul (rdHom L x h) n u

private theorem actY_inv {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) (w : VQ D) : actY L y (actY L y⁻¹ w) = w := by
  show L.rep _ (L.rep _ w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private theorem inv_actY {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) (w : VQ D) : actY L y⁻¹ (actY L y w) = w := by
  show L.rep ((y⁻¹ : GlobalTheory.LKCx.grp G β) : G.Cˣ × ℚˣ).1 (L.rep ((y : G.Cˣ × ℚˣ).1 : G.C) w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private noncomputable def placeY {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) {D'' : PLat D.O D.inv} (j'' : D''.La →+ VQ D) :
    D''.La →+ VQ D :=
  (LinearMap.toAddMonoidHom (actY L y)).comp j''

private theorem placeY_apply {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) {D'' : PLat D.O D.inv} (j'' : D''.La →+ VQ D)
    (u : D''.La) : placeY L y j'' u = actY L y (j'' u) := rfl

private theorem coordA_placeY (hR : RdAct) (B : GlobalTheory.LKCx.Form G) (y : GlobalTheory.LKCx.grp G B.β) {N : ℕ}
    {D'' : PLat D.O D.inv} {t'' : D.La → D''.La} {j'' : D''.La →+ VQ D} {h : G.GAf}
    (hc : IsCoordA L (trivX B) N D'' t'' j'' h) :
    IsCoordA L (trivX B) N D'' t'' (placeY L y j'') (B.toAf y * h) := by
  have key : ∀ w, rd L (trivX B) (B.toAf y * h) (actY L y w) = rd L (trivX B) h w := by
    intro w
    rw [hR p D G L B y (B.toAf y * h) h w]
    have e : (B.toAf y * h)⁻¹ * B.toAf y * h = 1 := by group
    rw [e, map_one, Module.End.one_apply]
  refine ⟨fun w => ?_, fun a => ?_⟩
  · have hw : w = actY L y (actY L y⁻¹ w) := (actY_inv L y w).symm
    rw [hw, key, ← hc.1 (actY L y⁻¹ w), ← hw]
    constructor
    · rintro ⟨r, u, hu⟩
      refine ⟨r, u, ?_⟩
      rw [placeY_apply] at hu
      rw [← map_nsmul, hu, inv_actY]
    · rintro ⟨r, u, hu⟩
      refine ⟨r, u, ?_⟩
      rw [placeY_apply, ← hu, map_nsmul, actY_inv]
  · obtain ⟨w1, hw1, e⟩ := hc.2 a
    exact ⟨w1, hw1, by rw [placeY_apply, key, e]⟩

private theorem locP_placeY {β : G.Cˣ} (PD : PDic L β) (y : GlobalTheory.LKCx.grp G β) {D'' : PLat D.O D.inv}
    {j'' : D''.La →+ VQ D} {hp : Gr G 1} (hl : IsLocP D'' j'' (PD.lat hp)) :
    IsLocP D'' (placeY L y j'') (PD.lat (GlobalTheory.LKCx.toP1 G β y * hp)) := by
  intro w
  have hw : w = actY L y (actY L y⁻¹ w) := (actY_inv L y w).symm
  rw [hw, PD.equiv y hp, ← hl (actY L y⁻¹ w), ← hw]
  constructor
  · rintro ⟨m, u, hm, hu⟩
    refine ⟨m, u, hm, ?_⟩
    rw [placeY_apply] at hu
    rw [← map_nsmul, hu, inv_actY]
  · rintro ⟨m, u, hm, hu⟩
    refine ⟨m, u, hm, ?_⟩
    rw [placeY_apply, ← hu, map_nsmul, actY_inv]

private theorem range_le {x : (AfP p ⊗[ℚ] G.C)ˣ} {N : ℕ} {D₁ D₂ : PLat D.O D.inv} {t₁ : D.La → D₁.La}
    {t₂ : D.La → D₂.La} {j₁ : D₁.La →+ VQ D} {j₂ : D₂.La →+ VQ D} {h : G.GAf} {M : AddSubgroup (VQ D)}
    (hc₁ : IsCoordA L x N D₁ t₁ j₁ h) (hc₂ : IsCoordA L x N D₂ t₂ j₂ h)
    (hl₁ : IsLocP D₁ j₁ M) (hl₂ : IsLocP D₂ j₂ M) (u : D₁.La) : ∃ u₂, j₂ u₂ = j₁ u := by
  obtain ⟨r, u₂, hu₂⟩ := (hc₂.1 (j₁ u)).2 ((hc₁.1 (j₁ u)).1 ⟨0, u, by simp⟩)
  obtain ⟨m, u₃, hm, hu₃⟩ := (hl₂ (j₁ u)).2 ((hl₁ (j₁ u)).1 ⟨1, u, Nat.coprime_one_left p, one_smul _ _⟩)
  have hcop : IsCoprime ((p ^ r : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left r hm.symm)
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨a • u₂ + b • u₃, ?_⟩
  calc j₂ (a • u₂ + b • u₃) = a • j₂ u₂ + b • j₂ u₃ := by rw [map_add (f := _), map_zsmul, map_zsmul]
    _ = (a * ((p ^ r : ℕ) : ℤ) + b * (m : ℤ)) • j₁ u := by
      rw [← hu₂, ← hu₃, add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul]
    _ = j₁ u := by rw [hab, one_smul]

private theorem mark_div {x : (AfP p ⊗[ℚ] G.C)ˣ} {N : ℕ} (hN0 : 0 < N) (hNp : N.Coprime p) {D₁ : PLat D.O D.inv}
    {j : D₁.La →+ VQ D} (hj : Function.Injective j) {h : G.GAf}
    (hc : ∀ w, (∃ (r : ℕ) (u : D₁.La), p ^ r • w = j u) ↔ rd L x h w ∈ LaHat D)
    (d : D₁.La) {w₃ : AfP p ⊗[ℚ] VQ D} (hw₃ : w₃ ∈ LaHat D) (hd : rd L x h (j d) = N • w₃) :
    ∃ e : D₁.La, d = N • e := by
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
  set w : VQ D := (N : ℚ)⁻¹ • j d with hwdef
  have hNw : N • w = j d := by
    rw [hwdef, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hN, one_smul]
  have e : rd L x h w = w₃ := by
    have h1 : (N : ℚ) • rd L x h w = (N : ℚ) • w₃ := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← rd_nsmul, hNw, hd]
    have h2 := congrArg (fun z => (N : ℚ)⁻¹ • z) h1
    simpa only [smul_smul, inv_mul_cancel₀ hN, one_smul] using h2
  obtain ⟨r, u, hu⟩ := (hc w).2 (e ▸ hw₃)
  have h3 : j (p ^ r • d) = j (N • u) := by
    rw [map_nsmul, map_nsmul, ← hNw, ← hu, smul_comm]
  have h4 := hj h3
  have hcop : IsCoprime (N : ℤ) ((p ^ r : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right r hNp)
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨a • d + b • u, ?_⟩
  calc d = (a * (N : ℤ) + b * ((p ^ r : ℕ) : ℤ)) • d := by rw [hab, one_smul]
    _ = N • (a • d + b • u) := by
      rw [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, h4, smul_add, smul_comm N a d,
        smul_comm N b u]

end UpperTheory.Gal.W2.LatticeIsomorphism

open UpperTheory.Gal.W2.LatticeIsomorphism

theorem UpperTheory.Gal.W2.latIso_of :
    UpperTheory.Gal.W2.RdAct → UpperTheory.Gal.W2.CoordKN → UpperTheory.Gal.W2.ClsScalar → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.LatIso := by
  intro hR hK hS hA p _ D G L B PD N hN hNp D' t D'' t'' j j'' a a'' N₁ N₂ t₁ t₂ hc₁ hc₂ hpl hpl'' hca hca''
    hlp hlp'' y
  have hcaY : IsCoordA L (trivX B) N D'' t'' (placeY L y j'') (B.toAf y * a''.1) := coordA_placeY L hR B y hca''
  have hlpY : IsLocP D'' (placeY L y j'') (PD.lat (GlobalTheory.LKCx.toP1 G B.β y * a''.2)) := locP_placeY L PD y hlp''
  constructor
  · rintro ⟨hm1, hm2⟩
    have hcaY' : IsCoordA L (trivX B) N D'' t'' (placeY L y j'') a.1 :=
      (hK p D G L (trivX B) N hN hNp D'' t'' (placeY L y j'') _ _ hcaY).2 (by rwa [← _root_.mul_assoc])
    have hlat : PD.lat a.2 = PD.lat (GlobalTheory.LKCx.toP1 G B.β y * a''.2) :=
      (PD.inj _ _).2 (by rwa [← _root_.mul_assoc])
    have hlpY' : IsLocP D'' (placeY L y j'') (PD.lat a.2) := by
      rw [hlat]
      exact hlpY
    have hex : ∀ u : D''.La, ∃ u', j u' = placeY L y j'' u := range_le L hcaY' hca hlpY' hlp
    have hex' : ∀ u' : D'.La, ∃ u, placeY L y j'' u = j u' := range_le L hca hcaY' hlp hlpY'
    choose f hf using hex
    have hinj := hpl.1
    have hadd : ∀ u v, f (u + v) = f u + f v := fun u v => hinj (by simp only [map_add (f := _), hf])
    have hsmul : ∀ (c : D.O) u, f (c • u) = c • f u := fun c u => hinj (by
      rw [hf, hpl.2.1, hf, placeY_apply, placeY_apply, hpl''.2.1, (hA p D G L B.β y).2.1])
    let fl : D''.La →ₗ[D.O] D'.La := { toFun := f, map_add' := hadd, map_smul' := hsmul }
    have hYinj : Function.Injective (placeY L y j'') := by
      intro u v huv
      rw [placeY_apply, placeY_apply] at huv
      have e := congrArg (actY L y⁻¹) huv
      rw [inv_actY, inv_actY] at e
      exact hpl''.1 e
    have hbij : Function.Bijective fl := by
      refine ⟨fun u v huv => hYinj ?_, fun u' => ?_⟩
      · rw [← hf, ← hf]
        exact congrArg j huv
      · obtain ⟨u, hu⟩ := hex' u'
        exact ⟨u, hinj ((hf u).trans hu)⟩
    let w := LinearEquiv.ofBijective fl hbij
    have hjw : ∀ u, j (w u) = actY L y (j'' u) := fun u => hf u
    obtain ⟨s, hs, hsf⟩ := hpl.2.2.2
    obtain ⟨s'', hs'', hsf''⟩ := hpl''.2.2.2
    have hy2 : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
    have hsc : ∀ u u' : D''.La, (((D'.EF (w u)) (w u') : ℤ) : ℚ) =
        s * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) / s'' * (((D''.EF u) u' : ℤ) : ℚ) := by
      intro u u'
      rw [hsf, hjw, hjw, (hA p D G L B.β y).1, hsf'']
      field_simp
    have hr := hS p D N₁ N₂ D' t₁ D'' t₂ hc₁ hc₂ w.toAddEquiv _ (by positivity) hsc
    have hiso : IsIsom D'' D' w := by
      intro u u'
      have e := hsc u u'
      rw [hr, _root_.one_mul] at e
      exact_mod_cast e
    refine ⟨w, ⟨hiso, fun a0 => ?_⟩, hjw⟩
    obtain ⟨w1, hw1, e1⟩ := hca.2 a0
    obtain ⟨w2, hw2, e2⟩ := hcaY'.2 a0
    have hd : rd L (trivX B) a.1 (j (w (t'' a0) - t a0)) = N • (w2 - w1) := by
      rw [map_sub, rd_sub, hjw, ← placeY_apply, e2, e1, smul_sub]
      abel
    obtain ⟨e, he⟩ := mark_div L hN hNp hinj hca.1 _ (sub_mem hw2 hw1) hd
    exact ⟨e, eq_add_of_sub_eq' he⟩
  · rintro ⟨w, ⟨hiso, hmark⟩, hjw⟩
    have hjY : ∀ u, placeY L y j'' u = j (w u) := fun u => (hjw u).symm
    have hcaY' : IsCoordA L (trivX B) N D'' t'' (placeY L y j'') a.1 := by
      refine ⟨fun w0 => ?_, fun a0 => ?_⟩
      · rw [← hca.1 w0]
        constructor
        · rintro ⟨r, u, hu⟩
          exact ⟨r, w u, by rw [hu, hjY]⟩
        · rintro ⟨r, u, hu⟩
          exact ⟨r, w.symm u, by rw [hu, hjY, LinearEquiv.apply_symm_apply]⟩
      · obtain ⟨e, he⟩ := hmark a0
        obtain ⟨w1, hw1, e1⟩ := hca.2 a0
        have he' : rd L (trivX B) a.1 (j e) ∈ LaHat D := (hca.1 (j e)).1 ⟨0, e, by simp⟩
        refine ⟨w1 + rd L (trivX B) a.1 (j e), add_mem hw1 he', ?_⟩
        rw [hjY, he, map_add (f := _), map_nsmul, rd_add, rd_nsmul, e1, smul_add, add_assoc]
    have hkn := (hK p D G L (trivX B) N hN hNp D'' t'' (placeY L y j'') _ _ hcaY).1 hcaY'
    have hlpY' : IsLocP D'' (placeY L y j'') (PD.lat a.2) := by
      intro w0
      rw [← hlp w0]
      constructor
      · rintro ⟨m, u, hm, hu⟩
        exact ⟨m, w u, hm, by rw [hu, hjY]⟩
      · rintro ⟨m, u, hm, hu⟩
        exact ⟨m, w.symm u, hm, by rw [hu, hjY, LinearEquiv.apply_symm_apply]⟩
    have hlat : PD.lat a.2 = PD.lat (GlobalTheory.LKCx.toP1 G B.β y * a''.2) := by
      ext w0
      rw [← hlpY' w0, ← hlpY w0]
    have hkh := (PD.inj _ _).1 hlat
    exact ⟨by rw [_root_.mul_assoc]; exact hkn, by rw [_root_.mul_assoc]; exact hkh⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRigid
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.rigid_of :
    UpperTheory.Gal.W2.Rigid := by
  intro O _ bar g ρ Λ N D' t P w h hN hfull hper ⟨hiso, hmark⟩ hPw
  obtain ⟨-, hinj, hd, hspan, Hm, -, hpos, hIm⟩ := hper
  let σw : Module.End ℤ D'.La := (w.toLinearMap.toAddMonoidHom).toIntLinearMap
  have hσ : ∀ a, σw a = w a := fun _ => rfl
  let hR : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := h.toLinearMap.restrictScalars ℝ
  let B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun u v => (hermForm Hm u v).im)
    (fun a b c => by simp [hermForm]) (fun r a b => by simp [hermForm])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add]) (fun r a b => by simp [hermForm, Matrix.mulVec_smul])
  have hB : B.compl₁₂ hR hR = B := by
    refine LinearMap.ext_on_range hspan fun a => LinearMap.ext_on_range hspan fun b => ?_
    show (hermForm Hm (h (P a)) (h (P b))).im = (hermForm Hm (P a) (P b)).im
    rw [← hPw, ← hPw, hIm, hIm, hiso]
  have hq : ∀ u, (hermForm Hm u u).re = B (Complex.I • u) u := fun u => by
    show _ = (hermForm Hm (Complex.I • u) u).im
    simp [hermForm]
  have hbd := GlobalTheory.ExpUnique.isBounded_sublevel (q := fun u => (hermForm Hm u u).re)
    (by unfold hermForm; fun_prop) (fun r u => by
      simp only [hq]
      rw [smul_comm, map_smul, map_smul, LinearMap.smul_apply, smul_smul, sq, smul_eq_mul]) hpos
  have key : σw = 1 := by
    refine GlobalTheory.ExpUnique.end_eq_one_of_invariant D'.La σw (fun a b hab => w.injective hab)
      (fun a => (hermForm Hm (P a) (P a)).re) (fun c => ?_) (fun a => ?_) N hN fun a => ?_
    · refine Set.Finite.of_finite_image (f := P) ((Metric.finite_isBounded_inter_isClosed
        (s := P.range) DiscreteTopology.isDiscrete (hbd c) AddSubgroup.isClosed_of_discrete).subset ?_) hinj.injOn
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨ha, a, rfl⟩
    · have h1 : h (Complex.I • P a) = Complex.I • h (P a) := map_smul h _ _
      simp only [hq, hσ, hPw]
      rw [← h1]
      have h2 := LinearMap.congr_fun₂ hB (Complex.I • P a) (P a)
      rw [LinearMap.compl₁₂_apply] at h2
      exact h2
    · obtain ⟨i, f, rfl⟩ := hfull a
      obtain ⟨e₀, he₀⟩ := hmark i
      refine ⟨e₀ + w f - f, ?_⟩
      have h3 : w (t i + N • f) = w (t i) + N • w f := by rw [map_add (f := _), map_nsmul]
      rw [hσ, h3, he₀, smul_sub, smul_add]
      abel
  intro u
  rw [← hσ, key]
  rfl
end

