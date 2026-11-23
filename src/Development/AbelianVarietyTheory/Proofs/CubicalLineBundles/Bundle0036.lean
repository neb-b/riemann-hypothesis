module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionFieldExt
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SingleMemSpanIffOfSelfDual
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem single_mem_span_iff_of_selfDual : ∀ (O R K La I : Type) [CommRing O] [CommRing R] [Field K] [Algebra R K] [AddCommGroup La] [Module O La] [Fintype I] [DecidableEq I] (τ₀ : O →+* R) (h : La → La → O) (ev dv : La → I → K) (n : ℕ) (x y : Fin n → La), (∀ a b, algebraMap R K (τ₀ (h a b)) = ∑ i, ev a i * dv b i) → (∀ a, ev a = ∑ m, algebraMap R K (τ₀ (h a (y m))) • ev (x m)) → Submodule.span K (Set.range ev) = ⊤ → ∀ (i : I) (t : K), Pi.single i t ∈ Submodule.span R (Set.range ev) ↔ ∀ b, t * dv b i ∈ (algebraMap R K).range := by
  intro O R K La I _ _ _ _ _ _ _ _ τ₀ h ev dv n x y hh hev hspan i t
  have hsum : ∀ b, ∑ j, (Pi.single i t : I → K) j * dv b j = t * dv b i := by
    intro b
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  constructor
  · intro hm b
    rw [← hsum b]
    generalize (Pi.single i t : I → K) = v at hm
    induction hm using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      exact ⟨_, hh a b⟩
    | zero => simp
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      exact add_mem hu hw
    | smul r u _ hu =>
      have : ∑ j, (r • u) j * dv b j = algebraMap R K r * ∑ j, u j * dv b j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def, _root_.mul_assoc]
      rw [this]
      exact mul_mem ⟨r, rfl⟩ hu
  · intro hb
    have key : ∀ v : I → K, v = ∑ m, (∑ j, v j * dv (y m) j) • ev (x m) := by
      intro v
      have hv : v ∈ Submodule.span K (Set.range ev) := hspan ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, rfl⟩ := hv
        simp only [← hh]
        exact hev a
      | zero => simp
      | add u w _ _ hu hw =>
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_smul]
        rw [← hu, ← hw]
      | smul r u _ hu =>
        simp only [Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, ← Finset.mul_sum, mul_smul,
          ← Finset.smul_sum]
        rw [← hu]
    rw [key (Pi.single i t)]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [hsum]
    obtain ⟨r, hr⟩ := hb (y m)
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TateIsoExistsAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_algClosure_lift {K k : Type} [Field K] [Field k] [IsAlgClosed k] (β : K →+* k) :
    ∃ j : AlgebraicClosure K →+* k, j.comp (algebraMap K (AlgebraicClosure K)) = β := by
  letI : Algebra K k := β.toAlgebra
  let f : AlgebraicClosure K →ₐ[K] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, RingHom.ext fun z => f.commutes z⟩

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

section Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}

def OnTors (e : ℕ → Q → Q → kˣ → Prop) (n : ℕ) (x y : Q) (c : kˣ) : Prop :=
  0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c

def tateIsoCongr {e e' : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    (h : ∀ n x y c, 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e' n x y c) : TateIso D k Q act e' :=
  { I with
    isom := fun n hn a b =>
      h n _ _ _ hn ((I.onto n hn _).2 ⟨a, rfl⟩) ((I.onto n hn _).2 ⟨b, rfl⟩) (I.isom n hn a b) }

theorem onTors_iff {Ω Q' : Type} [Field Ω] [Group Q'] (i : k →+* Ω) (r : Q →* Q') (hr : Function.Injective r)
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → Ωˣ → Prop}
    (h : ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 →
      (e n x y c ↔ e' n (r x) (r y) (Units.map i.toMonoidHom c))) (n : ℕ) (x y : Q) (c : kˣ) :
    OnTors e' n (r x) (r y) (Units.map i.toMonoidHom c) ↔ OnTors e n x y c := by
  unfold OnTors
  rw [← map_pow, ← map_pow, map_eq_one_iff r hr, map_eq_one_iff r hr]
  exact forall₃_congr fun hn hx hy => (h n x y c hn hx hy).symm

theorem onto_tors {Q' : Type} [Group Q'] (r : Q →* Q') (hr : Function.Injective r)
    (h : ∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) (n : ℕ) (hn : 0 < n) (z : Q') (hz : z ^ n = 1) :
    ∃ y : Q, y ^ n = 1 ∧ r y = z := by
  obtain ⟨x, rfl⟩ := h n z hn hz
  exact ⟨x, by rwa [← map_pow, map_eq_one_iff r hr] at hz, rfl⟩

end Abstract

theorem cmTorsionIsometry_transport_geometricPoint (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (D : Datum H) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A))
    (hm : ∀ c, IsMonHom (act c))
    {F Ω k : Type} [Field F] [Field Ω] [Field k] [IsAlgClosed F] [IsAlgClosed Ω] [IsAlgClosed k] [CharZero F]
    (i : F →+* Ω) (j : F →+* k) (x : Sp F ⟶ S) (y : Sp Ω ⟶ S) (z : Sp k ⟶ S)
    (hy : spMap i ≫ x = y) (hz : spMap j ≫ x = z)
    (I : TateIso D Ω (Over.mk y ⟶ P.A) (fun c y => y ≫ act c)
      (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c))) :
    ∃ I' : TateIso D k (Over.mk z ⟶ P.A) (fun c y => y ≫ act c)
      (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)),
      (∀ (n : ℕ) (u : F), 0 < n → (I.ζ n : Ω) = i u → (I'.ζ n : k) = j u) ∧
      ∀ (n : ℕ) a (s : 𝟙_ (Over S) ⟶ P.A), 0 < n → toUnit _ ≫ s = I.ev n a → toUnit _ ≫ s = I'.ev n a := by
  subst hy hz
  have key : ∀ (k' : Type) [Field k'] (l : F →+* k') (r : (Over.mk x ⟶ P.A) →* (Over.mk (spMap l ≫ x) ⟶ P.A)),
      (∀ y, (r y).left = spMap l ≫ y.left) →
      (∀ c y, r (y ≫ act c) = r y ≫ act c) ∧ ∀ s : 𝟙_ (Over S) ⟶ P.A, r (toUnit _ ≫ s) = toUnit _ ≫ s := by
    intro k' _ l r hr
    have h : ∀ y, r y = (Over.homMk (spMap l) rfl : Over.mk (spMap l ≫ x) ⟶ Over.mk x) ≫ y :=
      fun y => Over.OverMorphism.ext (hr y)
    exact ⟨fun c y => by rw [h, h, Category.assoc], fun s => by rw [h, ← Category.assoc, comp_toUnit]⟩
  obtain ⟨r, hr, rinj, ronto, rw'⟩ := _root_.GlobalTheory.exists_torsion_fieldExt hL S P F Ω i x
  obtain ⟨q, hq, qinj, qonto, qw⟩ := _root_.GlobalTheory.exists_torsion_fieldExt hL S P F k j x
  obtain ⟨I₀, h₀⟩ := TateIsoFieldExt.down D i r (act := fun c y => y ≫ act c)
    (e := OnTors fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)) rinj (onto_tors r rinj ronto)
    (key Ω i r hr).1 (fun c => by haveI := hm c; exact MonObj.one_comp (act c))
    (onTors_iff i r rinj rw') (tateIsoCongr I fun _ _ _ _ _ _ _ h _ _ _ => h)
  obtain ⟨I', h'⟩ := TateIsoFieldExt.up D j q (act' := fun c y => y ≫ act c)
    (e' := OnTors fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)) qinj (onto_tors q qinj qonto)
    (key k j q hq).1 (onTors_iff j q qinj qw) I₀
  refine ⟨tateIsoCongr I' fun _ _ _ _ hn hx hy h => h hn hx hy, fun n u hn hu => ?_, fun n a s hn hs => ?_⟩
  · have h1 : i (I₀.ζ n) = i u := (h₀ n hn).1.symm.trans hu
    exact (h' n hn).1.trans (congrArg j (i.injective h1))
  · have h1 : toUnit _ ≫ s = I₀.ev n a :=
      rinj (((key Ω i r hr).2 s).trans (hs.trans ((h₀ n hn).2 a)))
    exact ((key k j q hq).2 s).symm.trans ((congrArg q h1).trans ((h' n hn).2 a).symm)

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorPairingIdentityOfPureTensors
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.LamCalc

theorem isTensor_induction {S : Scheme.{0}} {O : Type} [CommRing O] {G A T : Over S} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} {M : Type} [AddCommGroup M] [Module O M]
    (t : Serre.IsTensor A b G a M) {P : (T ⟶ A) → Prop} (y : T ⟶ A)
    (tmul : ∀ (m : M) (x : T ⟶ G), P (x ≫ t.tmul m)) (mul : ∀ y z, P y → P z → P (y * z)) : P y := by
  refine t.induction_on y ?_ tmul mul
  have h := tmul 0 1
  rwa [t.tmul_zero, MonObj.comp_one] at h

theorem lamEq_of_tmul : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type) [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (b' : OAct O A') (M' : Type) [AddCommGroup M'] [Module O M'] (t' : Serre.IsTensor A' b' G a M') (B B' : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : LB B.left) (L' : LB B'.left) (f₁ : A ⟶ B) (f₂ : A' ⟶ B) (g₁ : A ⟶ B') (g₂ : A' ⟶ B'), L.IsLB → L'.IsLB → (∃ t : LB.Gen (Theta B L), t.IsGen) → (∃ t : LB.Gen (Theta B' L'), t.IsGen) → IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ →
  (∀ m m', LamEq L (t.tmul m ≫ f₁) (t'.tmul m' ≫ f₂) L' (t.tmul m ≫ g₁) (t'.tmul m' ≫ g₂)) → LamEq L f₁ f₂ L' g₁ g₂ := by
  intro S O _ G A _ _ _ _ a b M _ _ t A' _ _ b' M' _ _ t' B B' _ _ _ _ L L' f₁ f₂ g₁ g₂ hL hL' hT hT' _ _ _ _ h
  have key : ∀ (T : Over S) (x : T ⟶ A) (y : T ⟶ A'),
      LBIso (cubeLB B ![x ≫ f₁, y ≫ f₂] L) (cubeLB B' ![x ≫ g₁, y ≫ g₂] L') := by
    intro T x y
    refine isTensor_induction t
      (P := fun x => LBIso (cubeLB B ![x ≫ f₁, y ≫ f₂] L) (cubeLB B' ![x ≫ g₁, y ≫ g₂] L')) x
      (fun m u => ?_) (fun x x' hx hx' => ?_)
    · refine isTensor_induction t'
        (P := fun y => LBIso (cubeLB B ![(u ≫ t.tmul m) ≫ f₁, y ≫ f₂] L)
          (cubeLB B' ![(u ≫ t.tmul m) ≫ g₁, y ≫ g₂] L')) y (fun m' v => ?_) (fun y y' hy hy' => ?_)
      · simp only [Category.assoc]
        exact lbIso_of_lamEq (h m m') u v
      · simp only [MonObj.mul_comp]
        exact lbIso_cubeLB_mul_right_of hL hL' hT hT' hy hy'
    · simp only [MonObj.mul_comp]
      exact lbIso_cubeLB_mul_left_of hL hL' hT hT' hx hx'
  exact key _ (fst A A') (snd A A')

end GlobalTheory.LamCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegDualLineCmIdeal
section
noncomputable section

open NumberField Module ReciprocityTheory.GeometryOfNumbersTheory
open scoped nonZeroDivisors

namespace GlobalTheory.CM


open NumberField Module in
open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.CM.deg_ideal_smul {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K V) (Λ : Submodule (𝓞 K) V) {v : V} (hv : v ≠ 0)
    {m : (K →+* ℂ) → ℝ} (hm : ∀ s, 0 < m s) (hf : ∀ s, (h.form s v v).re = m s)
    {𝔠 : FractionalIdeal (𝓞 K)⁰ K} (h𝔠 : 𝔠 ≠ 0) (hΛ : ∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ t ∈ 𝔠) :
    _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ = -Real.log (FractionalIdeal.absNorm 𝔠) / finrank ℚ K - _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K m / 2 := by
  set φ : K →ₗ[𝓞 K] V := (LinearMap.toSpanSingleton K V v).restrictScalars (𝓞 K) with hφ
  have hφapp : ∀ t, φ t = t • v := fun t => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    simp only [hφapp] at hab
    exact smul_left_injective K hv hab
  have hΛmap : Λ = (𝔠 : Submodule (𝓞 K) K).map φ := by
    ext z
    rw [hΛ, Submodule.mem_map]
    constructor
    · rintro ⟨t, rfl, ht⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, rfl, ht⟩
  have hform : ∀ s, h.form s v v = (m s : ℂ) := by
    intro s
    have hc := h.conj_symm s v v
    apply Complex.ext
    · simp [hf s]
    · simp only [Complex.ofReal_im]
      exact Complex.conj_eq_iff_im.mp hc
  have hcFG : (𝔠 : Submodule (𝓞 K) K).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔠
  obtain ⟨r, w, hw⟩ := _root_.ReciprocityTheory.GeometryOfNumbersTheory.exists_isFullRankFamily_of_fg (𝔠 : Submodule (𝓞 K) K) hcFG
  have hw' := hw
  unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame at hw'
  obtain ⟨hwmem, hwli, hwspan⟩ := hw'
  have hrange : Set.range (fun i => φ (w i)) = φ '' Set.range w := Set.range_comp φ w
  have hframe : _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K Λ (fun i => φ (w i)) := by
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame
    refine ⟨fun i => ?_, ?_, ?_⟩
    · rw [hΛmap]; exact Submodule.mem_map_of_mem (hwmem i)
    · exact hwli.map' (LinearMap.toSpanSingleton K V v) (LinearMap.ker_toSpanSingleton K hv)
    · intro z hz
      rw [SetLike.mem_coe, hΛ] at hz
      obtain ⟨t, rfl, ht⟩ := hz
      have ht' : t ∈ Submodule.span K (Set.range w) := hwspan ht
      have hmem := Submodule.mem_map_of_mem (f := LinearMap.toSpanSingleton K V v) ht'
      rw [Submodule.map_span, ← Set.range_comp] at hmem
      exact hmem
  have hΛFG : Λ.FG := hΛmap ▸ hcFG.map φ
  have hrel : (Submodule.span (𝓞 K) (Set.range (fun i => φ (w i)))).toAddSubgroup.relIndex
      Λ.toAddSubgroup = (Submodule.span (𝓞 K) (Set.range w)).toAddSubgroup.relIndex
      (𝔠 : Submodule (𝓞 K) K).toAddSubgroup := by
    rw [hΛmap, hrange, ← Submodule.map_span, Submodule.map_toAddSubgroup,
      Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hgram : ∀ σ, h.gram σ (fun i => φ (w i)) = (_root_.GlobalTheory.lineHerm m hm).gram σ w := by
    intro σ
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram
    ext i j
    simp only [Matrix.of_apply, hφapp, _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_smul_left, _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.smul_right, hform]
    unfold _root_.GlobalTheory.lineHerm
    simp only
    ring
  calc _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ = _root_.ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily h Λ (fun i => φ (w i)) := _root_.ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily h hΛFG hframe
    _ = _root_.ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily (_root_.GlobalTheory.lineHerm m hm) (𝔠 : Submodule (𝓞 K) K) w := by
      unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily
      rw [hrel]
      simp_rw [hgram]
    _ = _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg (_root_.GlobalTheory.lineHerm m hm) (𝔠 : Submodule (𝓞 K) K) :=
      (_root_.ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily _ hcFG hw).symm
    _ = _ := _root_.GlobalTheory.deg_lineHerm m hm h𝔠


open NumberField Module in
open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.CM.two_mul_deg_dual_line : ∀ (E K V : Type) [Field E] [NumberField E] [IsCMField E]
    [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K V)
    (Λ : Submodule (𝓞 K) V) (v : V) (τ : E →+* K) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (β : E) (n : (K →+* ℂ) → ℝ), 𝔞 ≠ 0 → v ≠ 0 → (∀ s, 0 < n s) →
    (∀ s : E →+* ℂ, 0 < (s β).re ∧ (s β).im = 0) →
    (∀ s, (h.form s v v).re = (s (τ β)).re * n s) →
    (∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ ∀ b ∈ 𝔞, IsIntegral ℤ (t * τ (β * IsCMField.complexConj E b))) →
    2 * _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ = (2 * Real.log (FractionalIdeal.absNorm 𝔞 : ℚ) +
      Real.log |(Algebra.norm ℚ β : ℚ)|) / Module.finrank ℚ E - _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K n := by
  intro E K V _ _ _ _ _ _ _ _ _ h Λ v τ 𝔞 β n h𝔞 hv hn hβ hf hΛ
  have hβ0 : β ≠ 0 := by
    rintro rfl
    obtain ⟨s⟩ : Nonempty (E →+* ℂ) := inferInstance
    simpa using (hβ s).1
  set 𝔞' : FractionalIdeal (𝓞 E)⁰ E :=
    FractionalIdeal.spanSingleton (𝓞 E)⁰ β * _root_.GlobalTheory.conjFrac 𝔞 with h𝔞'def
  have h𝔞' : 𝔞' ≠ 0 :=
    mul_ne_zero (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
      (_root_.GlobalTheory.conjFrac_ne_zero h𝔞)
  obtain ⟨𝔟, h𝔟, h𝔟span, h𝔟log⟩ := _root_.GlobalTheory.exists_fractionalIdeal_eq_span_image τ h𝔞'
  have hm : ∀ s : K →+* ℂ, 0 < (s (τ β)).re * n s := fun s => mul_pos (hβ (s.comp τ)).1 (hn s)
  have hmemΛ : ∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ t ∈ 𝔟⁻¹ := by
    intro z
    rw [hΛ]
    refine exists_congr fun t => and_congr_right fun _ => ?_
    rw [FractionalIdeal.mem_inv_iff h𝔟]
    constructor
    · intro H y hy
      rw [← FractionalIdeal.mem_coe, h𝔟span] at hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, hx, rfl⟩ := hx
        rw [SetLike.mem_coe, h𝔞'def, FractionalIdeal.mem_singleton_mul] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [_root_.GlobalTheory.mem_conjFrac] at hz
        have key := H _ hz
        rw [show _root_.ReciprocityTheory.ChartRestriction.G.FD.cc z = IsCMField.complexConj E z from rfl,
          IsCMField.complexConj_apply_apply] at key
        exact (_root_.GlobalTheory.mem_one_fractionalIdeal_iff).2 key
      | zero => simp
      | add x y _ _ hx hy =>
        rw [mul_add, ← FractionalIdeal.mem_coe]
        rw [← FractionalIdeal.mem_coe] at hx hy
        exact add_mem hx hy
      | smul a x _ hx =>
        rw [mul_smul_comm, ← FractionalIdeal.mem_coe]
        exact Submodule.smul_mem _ a hx
    · intro H b hb
      rw [← _root_.GlobalTheory.mem_one_fractionalIdeal_iff]
      apply H
      rw [← FractionalIdeal.mem_coe, h𝔟span]
      apply Submodule.subset_span
      refine ⟨β * IsCMField.complexConj E b, ?_, rfl⟩
      rw [SetLike.mem_coe, h𝔞'def, FractionalIdeal.mem_singleton_mul]
      exact ⟨IsCMField.complexConj E b, _root_.GlobalTheory.cc_mem_conjFrac.2 hb, rfl⟩
  have hdeg := _root_.GlobalTheory.CM.deg_ideal_smul h Λ hv hm hf (inv_ne_zero h𝔟) hmemΛ
  have hsumE : ∑ s : E →+* ℂ, Real.log (s β).re = Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| := by
    rw [← Real.log_prod (fun s _ => ne_of_gt (hβ s).1)]
    congr 1
    have hprodC : ((∏ s : E →+* ℂ, (s β).re : ℝ) : ℂ) = (((Algebra.norm ℚ β : ℚ) : ℝ) : ℂ) := by
      push_cast
      have hre : ∀ s : E →+* ℂ, ((s β).re : ℂ) = s β := fun s =>
        Complex.ext (by simp) (by simp [(hβ s).2])
      simp_rw [hre]
      rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun s => s β) (fun σ => σ β)
        (fun s => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ β]
      simp
    have hprod : (∏ s : E →+* ℂ, (s β).re : ℝ) = ((Algebra.norm ℚ β : ℚ) : ℝ) := by
      exact_mod_cast hprodC
    rw [hprod, abs_of_pos]
    rw [← hprod]
    exact Finset.prod_pos fun s _ => (hβ s).1
  have hM : _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K (fun s => (s (τ β)).re * n s) =
      Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| / finrank ℚ E + _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K n := by
    have hsplit : _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K (fun s => (s (τ β)).re * n s) =
        _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K (fun s => ((s.comp τ) β).re) + _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K n := by
      unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog
      rw [← add_div, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      exact Real.log_mul (ne_of_gt (hβ (s.comp τ)).1) (ne_of_gt (hn s))
    have hres := _root_.GlobalTheory.meanLog_comp τ (fun s : E →+* ℂ => (s β).re)
    rw [hsplit, hres, ← hsumE]
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog
    rfl
  have hlog𝔞' : Real.log (FractionalIdeal.absNorm 𝔞' : ℝ) =
      Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| + Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) := by
    rw [h𝔞'def, map_mul, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, Rat.cast_abs,
      Real.log_mul, _root_.GlobalTheory.log_absNorm_conjFrac h𝔞]
    · exact abs_ne_zero.mpr (Rat.cast_ne_zero.mpr ((Algebra.norm_ne_zero_iff).mpr hβ0))
    · exact Rat.cast_ne_zero.mpr (fun h0 => _root_.GlobalTheory.conjFrac_ne_zero h𝔞
        (FractionalIdeal.absNorm_eq_zero_iff.mp h0))
  have hinv : -Real.log (FractionalIdeal.absNorm 𝔟⁻¹ : ℝ) / finrank ℚ K =
      Real.log (FractionalIdeal.absNorm 𝔟 : ℝ) / finrank ℚ K := by
    rw [map_inv₀, Rat.cast_inv, Real.log_inv, neg_neg]
  rw [hdeg, hinv, h𝔟log, hlog𝔞', hM]
  ring

end GlobalTheory.CM
end
end

