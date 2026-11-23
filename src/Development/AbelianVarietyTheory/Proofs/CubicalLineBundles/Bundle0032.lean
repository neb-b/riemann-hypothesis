module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.TensorBundle

open GlobalTheory.PrimNorm GlobalTheory.MulPull GlobalTheory.Serre

section Algebra

variable {O V W U I : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
  [AddCommGroup U] [Fintype I]

def gramForm (β : V →+ V →+ U) (p : I → W →ₗ[O] V) (g : I → I → O) (x y : W) : U :=
  ∑ k : I × I, β (g k.1 k.2 • p k.1 x) (p k.2 y)

variable {β : V →+ V →+ U} {p : I → W →ₗ[O] V} {g : I → I → O} {br : O ≃+* O}

theorem gramForm_add_left (x y z : W) : gramForm β p g (x + y) z = gramForm β p g x z + gramForm β p g y z := by
  simp only [gramForm, map_add (f := _), smul_add, AddMonoidHom.add_apply, Finset.sum_add_distrib]

theorem gramForm_add_right (x y z : W) : gramForm β p g x (y + z) = gramForm β p g x y + gramForm β p g x z := by
  simp only [gramForm, map_add (f := _), Finset.sum_add_distrib]

theorem gramForm_zero (y : W) : gramForm β p g 0 y = 0 := by
  simp [gramForm]

theorem gramForm_adj (ha : ∀ c x y, β (c • x) y = β x (br c • y)) (c : O) (x y : W) :
    gramForm β p g (c • x) y = gramForm β p g x (br c • y) := by
  simp only [gramForm, map_smul]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_comm, ha]

theorem gramForm_comm (hs : ∀ x y, β x y = β y x) (ha : ∀ c x y, β (c • x) y = β x (br c • y))
    (hg : ∀ i j, g j i = br (g i j)) (x y : W) : gramForm β p g x y = gramForm β p g y x :=
  Fintype.sum_equiv (Equiv.prodComm I I) _ _ fun k => by
    rw [ha, hs, ← hg]
    rfl

theorem gramForm_polar (hs : ∀ x y, β x y = β y x) (ha : ∀ c x y, β (c • x) y = β x (br c • y))
    (hg : ∀ i j, g j i = br (g i j)) {w : O} (hw : w + br w = 1) (x y : W) :
    gramForm β p g (x + y) (w • (x + y)) + -gramForm β p g x (w • x) + -gramForm β p g y (w • y) +
      gramForm β p g 0 (w • 0) = gramForm β p g x y := by
  have e : gramForm β p g x y = gramForm β p g x (w • y) + gramForm β p g y (w • x) := by
    rw [gramForm_comm hs ha hg y, gramForm_adj ha, ← gramForm_add_right, ← add_smul, hw, one_smul]
  rw [e, gramForm_zero, smul_add, gramForm_add_left, gramForm_add_right, gramForm_add_right]
  abel

theorem gramForm_pure (ha : ∀ c x y, β (c • x) y = β x (br c • y)) (hb : ∀ c, br (br c) = c)
    {x y : W} {u v : V} {s s' : I → O} (hx : ∀ i, p i x = s i • u) (hy : ∀ i, p i y = s' i • v) :
    gramForm β p g x y = β ((∑ k : I × I, br (s' k.2) * (g k.1 k.2 * s k.1)) • u) v := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_smul, map_sum, AddMonoidHom.finsetSum_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [hx, hy, mul_smul (br _), ha (br _), hb, mul_smul]

theorem hermitian_expand {M : Type} [AddCommGroup M] [Module O M] (h : M →ₗ[O] M →+ O)
    (hh : ∀ x y, h y x = br (h x y)) (e : I → M) (s s' : I → O) :
    ∑ k : I × I, br (s' k.2) * (h (e k.1) (e k.2) * s k.1) = h (∑ i, s i • e i) (∑ i, s' i • e i) := by
  have sm : ∀ c x y, h x (c • y) = br c * h x y := fun c x y => by
    rw [hh (c • y) x, map_smul, AddMonoidHom.smul_apply, smul_eq_mul, map_mul, ← hh]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum h, AddMonoidHom.finsetSum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sm, map_smul, AddMonoidHom.smul_apply, smul_eq_mul, mul_comm (s i)]

end Algebra

section Geometry

variable {S : Scheme.{0}} {O : Type} [CommRing O] {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A]
  [IsCommMonObj A] {L : LB G.left}

def lamForm (a : OAct O G) (hL : L.IsLB) (hT : ∃ t : LB.Gen (Theta G L), t.IsGen) (T : Over S) :
    Pts a T →+ Pts a T →+ Additive (PullClass L T.left) :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Additive.ofMul (diff₂ (ptCls L T) x.hom y.hom))
    fun y z => congrArg Additive.ofMul (diff₂_mul_right (diff₃_ptCls hL hT) x.hom y.hom z.hom))
    fun x y => AddMonoidHom.ext fun z => congrArg Additive.ofMul (diff₂_mul_left (diff₃_ptCls hL hT) x.hom y.hom z.hom)

variable {I : Type} [Fintype I]

def prodMap (f f' : I → (A ⟶ G)) (k : I × ULift.{0} (Finset (Fin 2))) : A.left ⟶ G.left :=
  (psum G ![f k.1, f' k.1] k.2.down).left

def prodExp (k : I × ULift.{0} (Finset (Fin 2))) : ℤ := (-1) ^ (2 - k.2.down.card)

def prodCls (L : LB G.left) (f f' : I → (A ⟶ G)) {Y : Scheme.{0}} (ψ : Y ⟶ A.left) : PullClass L Y :=
  ∏ k, cls L (ψ ≫ prodMap f f' k) ^ prodExp k

omit [GrpObj A] [IsCommMonObj A] in
theorem prodCls_left (f f' : I → (A ⟶ G)) {T : Over S} (x : T ⟶ A) :
    prodCls L f f' x.left = ∏ k, diff₂ (ptCls L T) (x ≫ f k) (x ≫ f' k) := by
  rw [prodCls, Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun k _ => prod_square x (f k) (f' k) (cls L)

end Geometry

theorem exists_tensor_bundle : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type) [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (br : O ≃+* O) (w : O) (L : LB G.left) (h : M →ₗ[O] M →+ O), Module.Finite O M → Module.Projective O M → w + br w = 1 → (∀ c, br (br c) = c) → (∀ x y, h y x = br (h x y)) → L.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∀ c, LamEq L (a.act c) (𝟙 G) L (𝟙 G) (a.act (br c))) →
  ∃ N : LB A.left, N.IsLB ∧ Out.Rigidified A N ∧ (∃ t : LB.Gen (Theta A N), t.IsGen) ∧ ∀ m m', LamEq N (t.tmul m) (t.tmul m') L (a.act (h m m')) (𝟙 G) := by
  intro S O _ G A _ _ _ _ a b M _ _ t br w L h _ _ hw hb hh hL hT ha
  obtain ⟨P⟩ := Summand.nonempty O M
  let c : Fin P.n → M →ₗ[O] O := fun i => LinearMap.proj i ∘ₗ P.incl
  let e : Fin P.n → M := fun i => P.proj (Pi.single i 1)
  have he : ∀ m, ∑ i, c i m • e i = m := fun m => by
    have : ∑ i, P.incl m i • (Pi.single i 1 : Fin P.n → O) = P.incl m := by
      ext j
      simp [Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, ← map_smul, ← map_sum]
    exact (congrArg P.proj this).trans congr($(P.proj_incl) m)
  let π : Fin P.n → (A ⟶ G) := fun i => t.mapLeft (IsTensor.self a) (c i)
  have hπ : ∀ i, IsLinearHom b a (π i) := fun i => t.isLinearHom_mapLeft _ _
  let g : Fin P.n → Fin P.n → O := fun i j => h (e i) (e j)
  let f : Fin P.n × Fin P.n → (A ⟶ G) := fun k => π k.1 ≫ a.act (g k.1 k.2)
  let f' : Fin P.n × Fin P.n → (A ⟶ G) := fun k => b.act w ≫ π k.2
  let B : ∀ T : Over S, Pts b T → Pts b T → Additive (PullClass L T.left) := fun T =>
    gramForm (lamForm a hL hT T) (fun i => Pts.post (hπ i) T) g
  have hs : ∀ (T : Over S) x y, lamForm a hL hT T x y = lamForm a hL hT T y x := fun T x y =>
    congrArg Additive.ofMul (diff₂_comm _ _)
  have hadj : ∀ (T : Over S) (r : O) x y, lamForm a hL hT T (r • x) y = lamForm a hL hT T x (br r • y) :=
    fun T r x y => by
      have := ha r
      unfold LamEq at this
      rw [Category.comp_id, Category.comp_id] at this
      exact congrArg Additive.ofMul (diff₂_ptCls_adj hL this x.hom y.hom)
  have hq : ∀ (T : Over S) (x : T ⟶ A), prodCls L f f' x.left = (B T (Pts.mk b x) (w • Pts.mk b x)).toMul :=
    fun T x => by
      rw [prodCls_left]
      refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_) (toMul_sum _ _).symm
      simp only [f, f', ← Category.assoc]
      rfl
  have h₂ : ∀ (T : Over S) (x y : T ⟶ A), diff₂ (fun q : T ⟶ A => prodCls L f f' q.left) x y =
      (B T (Pts.mk b x) (Pts.mk b y)).toMul := fun T x y => by
    simp only [diff₂, hq]
    exact congrArg Additive.toMul (gramForm_polar (hs T) (hadj T) (fun i j => hh _ _) hw (Pts.mk b x) (Pts.mk b y))
  refine ⟨LB.LinComb L (prodMap f f') prodExp, DVR.linComb_isLB _ hL _ _, ?_, ?_, fun m m' => ?_⟩
  · refine hasGen_nested (K' := PUnit) hL _ _ (fun _ => eSec A) (fun _ => 1) ?_
    rw [Fintype.prod_unique, zpow_one]
    refine (hq _ η[A]).trans ?_
    have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by simp [Hom.one_def]
    rw [e]
    exact congrArg Additive.toMul (gramForm_zero _)
  · refine hasGen_nested hL _ _ (thφ A (x3 A)) thε ((GlobalTheory.AbLaw.Cube.prod_theta (prodCls L f f')).trans
      ((prod_cub _ _ _ (prodCls L f f')).trans ?_))
    have e := diff₂_mul_left_eq (m := fun q : G3 A ⟶ A => prodCls L f f' q.left) (x3 A 0) (x3 A 1) (x3 A 2)
    rw [h₂, h₂, h₂, Pts.mk_mul] at e
    exact mul_eq_right.1 (e.symm.trans (congrArg Additive.toMul (gramForm_add_left _ _ _)))
  · refine lbIso_nested hL _ _ _ _ _ _ ((prod_square_id _ _ (prodCls L f f')).trans
      (Eq.trans ?_ (prod_square_id _ _ (cls L)).symm))
    have k : ∀ (u : G ⊗ G ⟶ G) (m : M) i,
        Pts.post (hπ i) _ (Pts.mk b (u ≫ t.tmul m)) = c i m • Pts.mk a u := fun u m i => Pts.ext (by
      simp only [Pts.hom_post, Pts.hom_mk, Pts.hom_smul, π, Category.assoc, IsTensor.tmul_mapLeft,
        IsTensor.self_tmul])
    rw [h₂, Category.comp_id]
    refine congrArg Additive.toMul ((gramForm_pure (hadj _) hb (k _ m) (k _ m')).trans ?_)
    rw [(hermitian_expand h hh e (fun i => c i m) fun i => c i m' :
      ∑ k : Fin P.n × Fin P.n, br (c k.2 m') * (g k.1 k.2 * c k.1 m) = _), he, he]
    rfl

end GlobalTheory.TensorBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueCmHermitianLatticeForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def kFun {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) : OK H :=
  (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : OK H) + (((ε : ℤ) * D.EF x y : ℤ) : OK H) * wK H

theorem kFun_coe {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) : ((kFun D ε x y : OK H) : 𝓞 E) =
    (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : 𝓞 E) + (((ε : ℤ) * D.EF x y : ℤ) : 𝓞 E) * H.w0 := by
  simp only [kFun, wK, Subalgebra.coe_add, Subalgebra.coe_mul, SubringClass.coe_intCast]

theorem kform_w0_sq (H : Host E) : H.w0 * H.w0 = H.w0 - (((1 + H.d) / 4 : ℕ) : 𝓞 E) := by
  have h := congrArg (fun a : OK H => (a : 𝓞 E)) (_root_.GlobalTheory.CM.OK_isDedekindDomain_and_projective E H).2.2.2.1
  simp only [wK, Subalgebra.coe_add, SubmonoidClass.coe_pow, SubringClass.coe_natCast] at h
  linear_combination h

theorem kform_bar_w0 (H : Host E) : H.bar H.w0 = 1 - H.w0 := by
  obtain ⟨br, h1, h2, -⟩ := (_root_.GlobalTheory.CM.OK_isDedekindDomain_and_projective E H).2.2.1
  have h := congrArg (fun a : OK H => (a : 𝓞 E)) h2
  simp only [Subalgebra.coe_add, h1, Subalgebra.coe_one] at h
  simp only [wK] at h
  linear_combination h

theorem kform_skew {H : Host E} (D : Datum H) (x y : D.La) : D.EF y x = - D.EF x y := by
  have h := D.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt] at h
  linarith

theorem kFun_add_left {H : Host E} (D : Datum H) (ε : ℤˣ) (x x' y : D.La) :
    kFun D ε (x + x') y = kFun D ε x y + kFun D ε x' y := by
  simp only [kFun, smul_add, map_add (f := _), LinearMap.add_apply]
  push_cast; ring

theorem kFun_add_right {H : Host E} (D : Datum H) (ε : ℤˣ) (x y y' : D.La) :
    kFun D ε x (y + y') = kFun D ε x y + kFun D ε x y' := by
  simp only [kFun, map_add (f := _)]
  push_cast; ring

theorem kFun_zsmul {H : Host E} (D : Datum H) (ε : ℤˣ) (m : ℤ) (x y : D.La) :
    kFun D ε (m • x) y = (m : OK H) * kFun D ε x y := by
  simp only [kFun, smul_comm H.w0 m x, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  push_cast; ring

theorem kFun_w0 {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) :
    kFun D ε (H.w0 • x) y = wK H * kFun D ε x y := by
  apply Subtype.ext
  have hw : H.w0 • H.w0 • x = H.w0 • x - (((1 + H.d) / 4 : ℕ) : ℤ) • x := by
    rw [smul_smul, kform_w0_sq, sub_smul, Nat.cast_smul_eq_nsmul, natCast_zsmul]
  have h2 := kform_w0_sq H
  rw [Subalgebra.coe_mul, kFun_coe, kFun_coe, hw]
  simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, wK]
  generalize ((1 + H.d) / 4 : ℕ) = N at *
  push_cast
  linear_combination (-((ε : ℤ) : 𝓞 E) * (D.EF x y : 𝓞 E)) * h2

theorem kFun_smul {H : Host E} (D : Datum H) (ε : ℤˣ) (a : OK H) (x y : D.La) :
    kFun D ε (a • x) y = a * kFun D ε x y := by
  obtain ⟨⟨m, n⟩, rfl, -⟩ := (_root_.GlobalTheory.CM.OK_isDedekindDomain_and_projective E H).2.1 a
  have : ((m : OK H) + (n : OK H) * wK H) • x = m • x + n • H.w0 • x := by
    rw [add_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]; rfl
  simp only
  rw [this, kFun_add_left, kFun_zsmul, kFun_zsmul, kFun_w0]; ring

def kLin {H : Host E} (D : Datum H) (ε : ℤˣ) : D.La →ₗ[OK H] D.La →+ OK H where
  toFun x := AddMonoidHom.mk' (kFun D ε x) (kFun_add_right D ε x)
  map_add' x x' := by ext1 y; exact kFun_add_left D ε x x' y
  map_smul' a x := by ext1 y; exact kFun_smul D ε a x y

theorem kLin_apply {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) : kLin D ε x y = kFun D ε x y := rfl

theorem kform_coeff_unique (H : Host E) {a b c d : ℤ}
    (h : (a : OK H) + (b : OK H) * wK H = (c : OK H) + (d : OK H) * wK H) : a = c ∧ b = d := by
  have := ((_root_.GlobalTheory.CM.OK_isDedekindDomain_and_projective E H).2.1 ((a : OK H) + (b : OK H) * wK H)).unique (y₁ := (a, b)) (y₂ := (c, d)) rfl h
  exact Prod.mk.inj this

theorem kLin_perfect {H : Host E} (D : Datum H) (ε : ℤˣ) (f : D.La →ₗ[OK H] OK H) :
    ∃! y, ∀ x, f x = kLin D ε x y := by
  have hε : (ε : ℤ) * ε = 1 := by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  choose c hc using fun a => ((_root_.GlobalTheory.CM.OK_isDedekindDomain_and_projective E H).2.1 a).exists
  let b : D.La →+ ℤ := AddMonoidHom.mk' (fun x => -(ε : ℤ) * (c (f x)).2) (by
    intro x x'
    have : (((c (f (x + x'))).1 : ℤ) : OK H) + ((c (f (x + x'))).2 : OK H) * wK H =
        (((c (f x)).1 + (c (f x')).1 : ℤ) : OK H) + (((c (f x)).2 + (c (f x')).2 : ℤ) : OK H) * wK H := by
      rw [← hc, map_add (f := _)]
      have h1 := hc (f x)
      have h2 := hc (f x')
      push_cast
      linear_combination h1 + h2
    rw [(kform_coeff_unique H this).2]; ring)
  obtain ⟨y, hy⟩ := D.unimod.2 b.toIntLinearMap
  have hb : ∀ x, (ε : ℤ) * D.EF x y = (c (f x)).2 := by
    intro x
    rw [kform_skew, hy]
    change (ε : ℤ) * -(-(ε : ℤ) * (c (f x)).2) = _
    linear_combination (c (f x)).2 * hε
  have hint : ∀ x, ∃ m : ℤ, f x - kFun D ε x y = m := by
    intro x
    refine ⟨(c (f x)).1 - (ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y), ?_⟩
    have h1 := hc (f x)
    rw [kFun, hb]
    push_cast
    linear_combination h1
  refine ⟨y, fun x => ?_, fun y' hy' => ?_⟩
  · obtain ⟨m, hm⟩ := hint x
    obtain ⟨m', hm'⟩ := hint (wK H • x)
    rw [map_smul, kFun_smul, smul_eq_mul, ← mul_sub, hm] at hm'
    have : ((0 : ℤ) : OK H) + (m : OK H) * wK H = (m' : OK H) + ((0 : ℤ) : OK H) * wK H := by
      push_cast; linear_combination hm'
    rw [(kform_coeff_unique H this).2] at hm
    rw [kLin_apply, ← sub_eq_zero, hm, Int.cast_zero]
  · apply D.unimod.1
    ext x
    have h1 := (hc (f x)).symm.trans (hy' x)
    have h2 := (kform_coeff_unique H h1).2
    rw [kform_skew D x y', kform_skew D x y]
    have h3 := hb x
    linear_combination (ε : ℤ) * (h2 + h3) + (D.EF x y' - D.EF x y) * hε

theorem exists_kForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ), ∃ h : D.La →ₗ[OK H] D.La →+ OK H, IsKForm D ε (fun x y => h x y) ∧ (∀ h' : D.La → D.La → OK H, IsKForm D ε h' → h' = fun x y => h x y) ∧ (∀ x y, ((h y x : OK H) : 𝓞 E) = H.bar (h x y : OK H)) ∧ (∀ (s : 𝓞 E) x y, h (s • x) y = h x (H.bar s • y)) ∧ (∀ x, ((h x x : OK H) : 𝓞 E) = (((ε : ℤ) * D.EF (H.w0 • x) x : ℤ) : 𝓞 E)) ∧ (∀ f : D.La →ₗ[OK H] OK H, ∃! y, ∀ x, f x = h x y) ∧ ∃ (n : ℕ) (x y : Fin n → D.La), ∀ a, a = ∑ i, h a (y i) • x i := by
  intro E _ _ _ H D ε
  refine ⟨kLin D ε, kFun_coe D ε, fun h' hh => ?_, fun x y => ?_, fun s x y => ?_, fun x => ?_,
    kLin_perfect D ε, ?_⟩
  · funext x y
    exact Subtype.ext ((hh x y).trans (kFun_coe D ε x y).symm)
  · have h1 : D.EF (H.w0 • y) x = D.EF (H.w0 • x) y - D.EF x y := by
      rw [D.adj, kform_bar_w0, sub_smul, one_smul, map_sub, kform_skew D x y, kform_skew D (H.w0 • x) y]
      ring
    rw [kLin_apply, kLin_apply, kFun_coe, kFun_coe, h1, kform_skew D x y, map_add (f := _), map_mul, map_intCast,
      map_intCast, kform_bar_w0]
    push_cast; ring
  · rw [kLin_apply, kLin_apply, kFun, kFun, smul_comm H.w0 s x, D.adj, D.adj s]
  · rw [kLin_apply, kFun_coe, D.alt]
    push_cast; ring
  · obtain ⟨h1, h2, -⟩ := (_root_.GlobalTheory.CM.OK_isDedekindDomain_and_projective E H).2.2.2.2.2 D.La D.fin D.proj
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' (OK H) D.La
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    choose y hy using fun i : Fin n => (kLin_perfect D ε ((LinearMap.proj i).comp s)).exists
    refine ⟨n, fun i => π (Pi.single i 1), y, fun a => ?_⟩
    have ha : π (s a) = a := LinearMap.congr_fun hs a
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← ha, ← Finset.univ_sum_single (s a), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    letI : SMul (OK H) (Fin n → OK H) := ⟨fun c v j => c * v j⟩
    rw [← hy, ← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    rfl

end GlobalTheory.CM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

section
variable {E K K' : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K']

theorem ringOfIntegers_hom_injective (τ : 𝓞 E →+* 𝓞 K) : Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  have : (RingHom.ker τ).IsPrime := RingHom.ker_isPrime τ
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

theorem existsUnique_extend_ringOfIntegers_hom (τ : 𝓞 E →+* 𝓞 K) :
    ∃! τ' : E →+* K, ∀ a : 𝓞 E, τ' a = τ a := by
  have hi : Function.Injective ((algebraMap (𝓞 K) K).comp τ) :=
    (RingOfIntegers.coe_injective).comp (ringOfIntegers_hom_injective τ)
  have hl : ∀ a : 𝓞 E, (IsFractionRing.lift hi : E →+* K) (algebraMap (𝓞 E) E a) = algebraMap (𝓞 K) K (τ a) :=
    fun a => IsFractionRing.lift_algebraMap (A := 𝓞 E) (K := E) hi a
  generalize (IsFractionRing.lift hi : E →+* K) = σ₀ at hl
  refine ⟨σ₀, hl, fun σ hσ => ?_⟩
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  exact (hσ a).trans (hl a).symm

theorem mapRingHom_bijective :
    Function.Bijective fun σ : E →+* K => (RingOfIntegers.mapRingHom σ : 𝓞 E →+* 𝓞 K) := by
  constructor
  · intro σ σ' h
    refine (existsUnique_extend_ringOfIntegers_hom (RingOfIntegers.mapRingHom σ)).unique (fun a => rfl) fun a => ?_
    have h' : RingOfIntegers.mapRingHom σ = RingOfIntegers.mapRingHom σ' := h
    rw [h']
    rfl
  · intro τ
    obtain ⟨σ, hσ⟩ := (existsUnique_extend_ringOfIntegers_hom τ).exists
    exact ⟨σ, RingHom.ext fun a => RingOfIntegers.ext (hσ a)⟩

theorem splits_iff_card : Splits E K ↔ Nat.card (E →+* K) = Module.finrank ℚ E := by
  rw [Splits, ← Nat.card_eq_of_bijective _ (mapRingHom_bijective (E := E) (K := K))]

theorem card_ringHom_le_finrank : Nat.card (E →+* K) ≤ Module.finrank ℚ E := by
  rw [Nat.card_congr (RingHom.equivRatAlgHom E K)]
  exact card_algHom_le_finrank ℚ E K

theorem comp_bijective_of_splits (j : K →+* K') (h : Splits E K) :
    Function.Bijective fun σ : E →+* K => j.comp σ := by
  have : Finite (E →+* K') := Finite.of_equiv _ (RingHom.equivRatAlgHom E K').symm
  have hi : Function.Injective fun σ : E →+* K => j.comp σ := fun σ σ' e =>
    RingHom.ext fun a => j.injective (DFunLike.congr_fun e a)
  refine hi.bijective_of_nat_card_le ?_
  rw [splits_iff_card.1 h]
  exact card_ringHom_le_finrank

end

theorem splits_basic : ∀ (E : Type) [Field E] [NumberField E], (∃ k : IntermediateField ℚ ℂ, FiniteDimensional ℚ k ∧ ∀ (τ : E →+* ℂ) a, τ a ∈ k) ∧ (∀ (k : IntermediateField ℚ ℂ) [NumberField k], (∀ (τ : E →+* ℂ) a, τ a ∈ k) → Splits E k) ∧ ∀ (K : Type) [Field K] [NumberField K], (Splits E K ↔ Nat.card (E →+* K) = Module.finrank ℚ E) ∧ (∀ τ : 𝓞 E →+* 𝓞 K, ∃! τ' : E →+* K, ∀ a : 𝓞 E, τ' a = τ a) ∧ ∀ (K' : Type) [Field K'] [NumberField K'] (j : K →+* K'), Splits E K → Splits E K' ∧ Function.Bijective fun τ : 𝓞 E →+* 𝓞 K => (RingOfIntegers.mapRingHom j).comp τ := by
  intro E _ _
  refine ⟨⟨IntermediateField.normalClosure ℚ E ℂ, inferInstance, fun τ a => ?_⟩, fun k _ hk => ?_,
    fun K _ _ => ⟨splits_iff_card, existsUnique_extend_ringOfIntegers_hom, fun K' _ _ j h => ⟨?_, ?_⟩⟩⟩
  · exact AlgHom.fieldRange_le_normalClosure τ.toRatAlgHom ⟨a, rfl⟩
  · rw [splits_iff_card, ← Embeddings.card E ℂ, ← Nat.card_eq_fintype_card]
    refine Nat.card_eq_of_bijective (fun σ => (algebraMap k ℂ).comp σ) ⟨fun σ σ' e => ?_, fun τ => ?_⟩
    · exact RingHom.ext fun a => (algebraMap k ℂ).injective (DFunLike.congr_fun e a)
    · exact ⟨τ.codRestrict k (hk τ), RingHom.ext fun a => rfl⟩
  · rw [splits_iff_card, ← Nat.card_eq_of_bijective _ (comp_bijective_of_splits j h)]
    exact splits_iff_card.1 h
  · have e : ((fun τ : 𝓞 E →+* 𝓞 K => (RingOfIntegers.mapRingHom j).comp τ) ∘
        fun σ : E →+* K => (RingOfIntegers.mapRingHom σ : 𝓞 E →+* 𝓞 K)) =
        (fun σ : E →+* K' => (RingOfIntegers.mapRingHom σ : 𝓞 E →+* 𝓞 K')) ∘ fun σ : E →+* K => j.comp σ := by
      funext σ
      exact RingHom.ext fun a => rfl
    rw [← Function.Bijective.of_comp_iff _ (mapRingHom_bijective (E := E) (K := K)), e]
    exact mapRingHom_bijective.comp (comp_bijective_of_splits j h)

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.GramStdBasisPosDefAndHq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem gram_stdBasis_posDef_and_hq :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (h : HermFam K (Fin n → K)) (s : K →+* ℂ), (h.gram s (fun i => Pi.single i 1) : Matrix (Fin n) (Fin n) ℂ).PosDef ∧ ∀ c, ReciprocityTheory.MultiplicativeHeights.hq (h.gram s (fun i => Pi.single i 1)) (ReciprocityTheory.MultiplicativeHeights.embVec s c) = (h.form s c c).re := by
  intro K _ _ n h s
  refine ⟨h.posDef s n _ ?_, fun c => ?_⟩
  · have hb := (Pi.basisFun K (Fin n)).linearIndependent
    have he : (⇑(Pi.basisFun K (Fin n)) : Fin n → Fin n → K) = fun i => Pi.single i 1 := by
      funext i; exact Pi.basisFun_apply K (Fin n) i
    rwa [he] at hb
  · have hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → K) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hx := h.form_expand s c (fun i => Pi.single i 1)
    rw [← hc] at hx
    rw [hx, ReciprocityTheory.MultiplicativeHeights.hq]
    congr 1
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ReciprocityTheory.MultiplicativeHeights.embVec, Pi.star_apply,
      Complex.star_def]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem hasType_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap f)) (ρ : R) (p q : ℕ), (Function.Injective f → HasType H t.act ρ p q → HasType H t'.act (f ρ) p q) ∧ ((∀ (k : Type) [Field k] (β : R →+* k), Function.Injective β → ∃ β' : R' →+* k, β'.comp f = β ∧ Function.Injective β') → HasType H t'.act (f ρ) p q → HasType H t.act ρ p q) := by
  intro E _ _ _ H R R' _ _ f t t' m ρ p q
  have key : ∀ (k : Type) [Field k] (β' : R' →+* k) (τ : 𝓞 E →+* k) (n : ℕ),
      LieMult t'.act (spMap β') τ n ↔ LieMult t.act (spMap (β'.comp f)) τ n := fun k _ β' τ n => by
    have e : spMap β' ≫ spMap f = spMap (β'.comp f) := (Spec.map_comp _ _).symm
    rw [← e]
    exact LiePull.lieMult_pull _ _ _ t.G t'.G (spMap f) m.cm.F t.act t'.act m.cart m.act k _ τ n
  refine ⟨fun hf h k _ _ β' hβ' τ => ?_, fun hext h k _ _ β hβ τ => ?_⟩
  · rw [key, key]
    exact h k (β'.comp f) (hβ'.comp hf) τ
  · obtain ⟨β', rfl, hβ'⟩ := hext k β hβ
    rw [← key, ← key]
    exact h k β' hβ' τ

end GlobalTheory.CM
end

