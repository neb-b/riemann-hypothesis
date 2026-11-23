module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0024

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleSnapper
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

theorem eulerChar_eq_finrank_H0 {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (F : SubSystem k x Ω) (hF : ∀ i, 1 ≤ i → Subsingleton (F.H i)) :
    eulerChar k F = Module.finrank k (F.H 0) := by
  unfold eulerChar
  rw [Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp
  · intro i _
    have := hF (i + 1) (by omega)
    simp [Module.finrank_zero_of_subsingleton]

theorem VeryAmpleSnapper.proof (hF : SnapperFinite.Statement.{u, w, w}) (hS : Snapper.Statement.{u, w, w})
    (hV : TwistVanishAll.Statement.{u, w}) (hA : AmpleVanish.Statement.{u, w, w}) :
    VeryAmpleSnapper.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb hZ hNb
  obtain ⟨r, h, hh⟩ := hNb
  have hx : x ≠ 0 := by
    obtain ⟨i, hi⟩ := hZ.relevant
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X] at hi
    exact fun h0 => hi (congrFun h0 i)
  set O := twistBundle k x 0
  have hsys : ∀ (a : ℕ) (c : ℤ), (O.toSubSystem.twistPows 1 (fun j => (![Nb] j).toSubSystem)
      (fun _ => a)).twist (twistSys k x c) = twistMul Nb.toSubSystem a c := by
    intro a c
    change ((twistSys k x 0).twist (Nb.toSubSystem.pow a)).twist _ = _
    rw [twistSys_zero_twist]
    rfl
  have hpt : ∀ a c : ℚ, (Fin.snoc (α := fun _ => ℚ) (fun _ : Fin 1 => a) c : Fin 2 → ℚ) = ![a, c] := by
    intro a c; funext i; fin_cases i <;> rfl
  have h0 : ∀ F : SubSystem k x Ω, Module.finrank k (F.H 0) = Module.finrank k F.secs := fun F =>
    (CechZerothCohomologySections.proof k Ω N x Ω F hx).some.finrank_eq
  obtain ⟨Q, hQ, hχ⟩ := hS k Ω N x e hZ Ω O.toSubFamily O.fg 1 ![Nb]
  obtain ⟨c₀, hc₀⟩ := hV k Ω N x O Nb r h hh.mem_secs hh.generates
  obtain ⟨a₀, ha₀⟩ := hA k Ω N x Ω O.toSubFamily O.fg Nb ⟨r, h, hh⟩
  refine ⟨fun a c => ?_, Q, c₀, hQ, fun a c hc => ?_, ?_⟩
  · have := hF k Ω N x Ω O.toSubFamily O.fg 1 ![Nb] (fun _ => a) c 0
    rw [hsys] at this
    exact (CechZerothCohomologySections.proof k Ω N x Ω _ hx).some.finiteDimensional
  · have hv : ∀ i, 1 ≤ i → Subsingleton ((twistMul Nb.toSubSystem a c).H i) := by
      intro i hi
      have := hc₀ i a c hi hc
      change Subsingleton ((((twistSys k x 0).twist (Nb.toSubSystem.pow a)).twist _).H i) at this
      rwa [twistSys_zero_twist] at this
    have := hχ (fun _ => a) c
    rw [hsys, hpt, eulerChar_eq_finrank_H0 _ hv, h0] at this
    exact_mod_cast this
  · filter_upwards [eventually_ge_atTop a₀] with a ha
    have hv : ∀ i, 1 ≤ i → Subsingleton ((Nb.toSubSystem.pow a).H i) := by
      intro i hi
      have := ha₀ i a hi ha
      change Subsingleton (((twistSys k x 0).twist (Nb.toSubSystem.pow a)).H i) at this
      rwa [twistSys_zero_twist] at this
    have := hχ (fun _ => a) 0
    rw [hsys, hpt, twistMul, SubSystem.twist_twistSys_zero, eulerChar_eq_finrank_H0 _ hv, h0] at this
    exact_mod_cast this

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsVeryAmpleZFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u v w

def VeryAmpleZExtend.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (H : SubSystem S x Ω) (r : ℕ) (h : Fin (r + 1) → Ω), (∀ l, h l ∈ H.secs) →
    ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 → ∀ c ∈ ampleRing H 1 (h j), ∀ K : Chart x,
      (∀ I : Chart x, ∃ e : ℕ, c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H 1 (h j) I) →
      ∀ f ∈ F.sub K, ∀ᶠ M in atTop, c ^ M • f ∈ secsOnZ F.toSubSystem H h J

def VeryAmpleZChartSpan.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubSystem S x E) (H : SubSystem S x Ω) (r : ℕ) (h : Fin (r + 1) → Ω), (∀ l, h l ∈ H.secs) →
    ∀ (I : Chart x) (J : Chart h) (g : Finset E), F.sub I ≤ Submodule.span (chartRing S x I) (g : Set E) →
      ∀ e ∈ secsOnZChart F H h I J, ∃ β : E → Ω,
        (∀ y ∈ g, β y ∈ ampleChart H J.1.card (xProd J) I) ∧ e = ∑ y ∈ g, β y • y

def VeryAmpleZChartRing.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy H.toSubSystem h →
    ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 → ∀ c ∈ ampleRing H.toSubSystem 1 (h j), ∀ K : Chart x,
      (∀ I : Chart x, ∃ e : ℕ,
        c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H.toSubSystem 1 (h j) I) →
      ∀ α ∈ ampleChart H.toSubSystem J.1.card (xProd J) K, ∀ᶠ M in atTop, c ^ M * α ∈ chartRing S h J

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SubFamilyTwistPowSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def SubFamilyTwistPow.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (Q : SubFamily S x Ω) (a : ℕ),
    ∃ G : SubFamily S x E, G.toSubSystem = F.twist (Q.pow a)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSplitLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Pointwise AddMonoidAlgebra

noncomputable section

universe u w

section Loc

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)

theorem map_C_mem_monos {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) :
    MvPolynomial.map (C : S →+* MvPolynomial (Fin (r + 1)) S) s ∈ monos (S := MvPolynomial (Fin (r + 1)) S) I := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]; exact X_mem_monos hi
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem eval_ne_zero_of_subset {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) {s : Poly S N}
    (hs : s ∈ monos I) : aeval x s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [aeval_X]
    exact (mem_support x).mp (hI hi)
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_ne_zero ha hb

theorem xyHom_of_mem_monos {I : Finset (Fin (N + 1))} {s : Poly (MvPolynomial (Fin (r + 1)) S) N}
    (hs : s ∈ monos I) : ∃ s₀ ∈ monos (S := S) I, ∃ e : ℕ, s₀.IsHomogeneous e ∧
      s = MvPolynomial.map (C : S →+* MvPolynomial (Fin (r + 1)) S) s₀ ∧
      xyHom S x η s = single ((0 : ℤ), (e : ℤ)) (aeval x s₀) := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨X i, X_mem_monos hi, 1, isHomogeneous_X S i, (map_X _ _).symm,
      by rw [xyHom_X, aeval_X, Nat.cast_one]⟩
  | one =>
    exact ⟨1, one_mem _, 0, isHomogeneous_one _ _, (map_one _).symm,
      by rw [map_one, map_one, AddMonoidAlgebra.one_def]; rfl⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a₀, ha₀, ea, hae, rfl, hxa⟩ := ha
    obtain ⟨b₀, hb₀, eb, hbe, rfl, hxb⟩ := hb
    refine ⟨a₀ * b₀, mul_mem ha₀ hb₀, ea + eb, hae.mul hbe, (map_mul _ _ _).symm, ?_⟩
    rw [map_mul, hxa, hxb, single_mul_single, map_mul]
    congr 1

theorem isUnit_xyHom {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    {s : Poly (MvPolynomial (Fin (r + 1)) S) N} (hs : s ∈ monos I) : IsUnit (xyHom S x η s) := by
  obtain ⟨s₀, hs₀, e, -, -, h⟩ := xyHom_of_mem_monos η hs
  rw [h]
  have hv := eval_ne_zero_of_subset hI hs₀
  refine isUnit_iff_exists_inv.mpr ⟨single ((0 : ℤ), -(e : ℤ)) (aeval x s₀)⁻¹, ?_⟩
  rw [single_mul_single, mul_inv_cancel₀ hv, AddMonoidAlgebra.one_def]
  congr 1
  ext <;> simp

variable (M₀ : FinGradedSub (S := S) (x := x) Ω)

theorem locEmb_isUnit {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    (s : monos (S := MvPolynomial (Fin (r + 1)) S) I) :
    IsUnit (algebraMap (Poly (MvPolynomial (Fin (r + 1)) S) N)
      (Module.End (Poly (MvPolynomial (Fin (r + 1)) S) N) (UT x η)) (s : Poly _ N)) := by
  rw [Module.End.isUnit_iff]
  have hu : IsUnit (UT.ofL (x := x) (η := η) (xyHom S x η s)) := isUnit_xyHom η hI s.2
  have : ⇑(algebraMap (Poly (MvPolynomial (Fin (r + 1)) S) N)
      (Module.End (Poly (MvPolynomial (Fin (r + 1)) S) N) (UT x η)) (s : Poly _ N)) =
      fun v => UT.ofL (x := x) (η := η) (xyHom S x η s) * v := by
    funext v; rfl
  rw [this]
  exact hu.unit.mulLeft_bijective

def locEmb (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I →ₗ[Poly (MvPolynomial (Fin (r + 1)) S) N] UT x η :=
  LocalizedModule.lift (monos I) (twSub η M₀).subtype (locEmb_isUnit η hI)

theorem xyHom_mul_locEmb_mk {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) (m : TwM η M₀)
    (s : monos (S := MvPolynomial (Fin (r + 1)) S) I) :
    xyHom S x η s * UT.toL (locEmb η M₀ I hI (LocalizedModule.mk m s)) = m.val := by
  have h0 : locEmb η M₀ I hI (LocalizedModule.mk m s) =
      (locEmb_isUnit η hI s).unit⁻¹.1 ((twSub η M₀).subtype m) :=
    LocalizedModule.lift_mk _ _ _ _ _
  rw [h0]
  have key := congrArg (fun f : Module.End (Poly (MvPolynomial (Fin (r + 1)) S) N) (UT x η) =>
    f ((twSub η M₀).subtype m)) (IsUnit.mul_val_inv (locEmb_isUnit η hI s))
  simp only [Module.End.mul_apply, Module.End.one_apply] at key
  exact key

theorem locEmb_mk {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) (m : TwM η M₀)
    (s : monos (S := MvPolynomial (Fin (r + 1)) S) I) {e : ℕ} {v : Ω}
    (h : xyHom S x η s = single ((0 : ℤ), (e : ℤ)) v) (hv : v ≠ 0) :
    UT.toL (locEmb η M₀ I hI (LocalizedModule.mk m s)) = single ((0 : ℤ), -(e : ℤ)) v⁻¹ * m.val := by
  have key := xyHom_mul_locEmb_mk η M₀ hI m s
  rw [h] at key
  rw [← key, ← mul_assoc, single_mul_single, inv_mul_cancel₀ hv]
  have : single (((0 : ℤ), -(e : ℤ)) + ((0 : ℤ), (e : ℤ))) (1 : Ω) = 1 := by
    rw [AddMonoidAlgebra.one_def]; congr 1; ext <;> simp
  rw [this, one_mul]

theorem locEmb_smul' {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) (c : MvPolynomial (Fin (r + 1)) S)
    (w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I) :
    UT.toL (locEmb η M₀ I hI (c • w)) = yHom S η c * UT.toL (locEmb η M₀ I hI w) := by
  change UT.toL (locEmb η M₀ I hI ((algebraMap _ (Poly (MvPolynomial (Fin (r + 1)) S) N) c) • w)) = _
  rw [LinearMap.map_smul, UT.smul_def, MvPolynomial.algebraMap_eq, xyHom_C]

theorem locEmb_injective {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) :
    Function.Injective (locEmb η M₀ I hI) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  induction w using LocalizedModule.induction_on with
  | h m s =>
    have key := xyHom_mul_locEmb_mk η M₀ hI m s
    rw [hw] at key
    have hm : m = 0 := TwM.val_injective (by rw [← key, TwM.val_zero]; exact mul_zero _)
    rw [hm, LocalizedModule.zero_mk]
    rfl

theorem locEmb_locRes {I J : Finset (Fin (N + 1))} (hI : I ⊆ support x) (hJ : J ⊆ support x) (h : I ⊆ J)
    (w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I) :
    locEmb η M₀ J hJ (locRes h w) = locEmb η M₀ I hI w := by
  induction w using LocalizedModule.induction_on with
  | h m s =>
    rw [locRes_mk]
    have hu := isUnit_xyHom η hJ (monos_mono h s.2)
    have k1 := xyHom_mul_locEmb_mk η M₀ hJ m ⟨(s : Poly _ N), monos_mono h s.2⟩
    have k2 := xyHom_mul_locEmb_mk η M₀ hI m s
    exact hu.mul_left_cancel (k1.trans k2.symm)

theorem twLocMod_subsingleton {J : Finset (Fin (N + 1))} (hJ : ¬ J ⊆ support x) :
    Subsingleton (LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) J) := by
  obtain ⟨i, hiJ, hi⟩ := Finset.not_subset.mp hJ
  have hxi : x i = 0 := by
    by_contra h; exact hi ((mem_support x).mpr h)
  have hX : ∀ m : TwM η M₀, (X i : Poly (MvPolynomial (Fin (r + 1)) S) N) • m = 0 := fun m =>
    TwM.val_injective (by rw [TwM.val_smul, xyHom_X, hxi, single_zero, zero_mul, TwM.val_zero])
  have hz : ∀ w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) J, w = 0 := by
    intro w
    induction w using LocalizedModule.induction_on with
    | h m s =>
      change (LocalizedModule.mk m s : LocalizedModule (monos J) (TwM η M₀)) =
        (0 : LocalizedModule (monos J) (TwM η M₀))
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
      refine ⟨⟨X i, X_mem_monos hiJ⟩, ?_⟩
      rw [smul_zero, smul_zero]
      exact hX _
  exact ⟨fun w w' => by rw [hz w, hz w']⟩

def LocGood (c : ℤ) (I : Finset (Fin (N + 1))) (W : LaurUT Ω) : Prop :=
  ∀ b : ℤ, W.coeff (b, c) ∈ twLocPart η M₀ b c I

theorem locGood_yHom_mul {c : ℤ} {I : Finset (Fin (N + 1))} (c' : MvPolynomial (Fin (r + 1)) S)
    {W : LaurUT Ω} (hW : LocGood η M₀ c I W) : LocGood η M₀ c I (yHom S η c' * W) := by
  induction c' using MvPolynomial.induction_on generalizing W with
  | C a =>
    intro b
    rw [yHom_C, coeff_single_mul_sub, sub_zero]
    have := Submodule.smul_mem _ a (hW b)
    rwa [Algebra.smul_def] at this
  | add p q hp hq =>
    intro b
    rw [map_add (f := _), add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact add_mem (hp hW b) (hq hW b)
  | mul_X p j hp =>
    rw [map_mul, mul_assoc]
    apply hp
    intro b
    rw [yHom_X, coeff_single_mul_sub]
    have := twLocPart_eta_mul η M₀ j (hW (b - 1))
    simpa using this

theorem locGood_locEmb (I : StdCell N) (hI : I.1 ⊆ support x) {c : ℤ}
    {w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I.1} (hw : w ∈ degLoc (twGraded η M₀) c I) :
    LocGood η M₀ c I.1 (UT.toL (locEmb η M₀ I.1 hI w)) := by
  refine Submodule.span_induction (p := fun w _ => LocGood η M₀ c I.1 (UT.toL (locEmb η M₀ I.1 hI w)))
    ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨m, s, a, e, -, hse, -, rfl⟩
    obtain ⟨s₀, hs₀, e', hs₀e, hss, hxs⟩ := xyHom_of_mem_monos η s.2
    have hv := eval_ne_zero_of_subset hI hs₀
    have hne : (s : Poly (MvPolynomial (Fin (r + 1)) S) N) ≠ 0 := fun h0 => hv (by
      rw [h0, map_zero] at hxs
      have := congrArg (fun W : LaurUT Ω => W.coeff ((0 : ℤ), (e' : ℤ))) hxs
      simpa using this.symm)
    have h1 : (s : Poly (MvPolynomial (Fin (r + 1)) S) N).IsHomogeneous e' := hss ▸ hs₀e.map C
    obtain rfl : e' = e := h1.inj_right hse hne
    intro b
    rw [locEmb_mk η M₀ hI m s hxs hv, coeff_single_mul_sub]
    have hidx : ((b, c) : ℤ × ℤ) - ((0 : ℤ), -(e' : ℤ)) = (b, c + e') := by ext <;> simp
    rw [hidx]
    exact Submodule.subset_span ⟨m.val.coeff (b, c + e'), s₀, c + e', e', hs₀, hs₀e, m.isTw (b, c + e'),
      by ring, rfl⟩
  · intro b; rw [map_zero]; exact Submodule.zero_mem _
  · intro u v _ _ hu hv b
    rw [map_add (f := _)]
    change (UT.toL _ + UT.toL _).coeff _ ∈ _
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact add_mem (hu b) (hv b)
  · intro c' u _ hu
    rw [locEmb_smul']
    exact locGood_yHom_mul η M₀ c' hu

theorem exists_locEmb_eq (I : StdCell N) (hI : I.1 ⊆ support x) {b c : ℤ} {y : Ω}
    (hy : y ∈ twLocPart η M₀ b c I.1) :
    ∃ w ∈ degLoc (twGraded η M₀) c I, UT.toL (locEmb η M₀ I.1 hI w) = single (b, c) y := by
  refine Submodule.span_induction (p := fun y _ => ∃ w ∈ degLoc (twGraded η M₀) c I,
    UT.toL (locEmb η M₀ I.1 hI w) = single (b, c) y) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z, s₀, a, e, hs₀, hse, hz, hae, rfl⟩
    let m : TwM η M₀ := TwM.mk (single (b, a) z) (isTw_single η M₀ hz)
    let s : monos (S := MvPolynomial (Fin (r + 1)) S) I.1 :=
      ⟨MvPolynomial.map (C : S →+* MvPolynomial (Fin (r + 1)) S) s₀, map_C_mem_monos hs₀⟩
    refine ⟨LocalizedModule.mk m s, Submodule.subset_span ⟨m, s, a, e, ?_, hse.map C, hae, rfl⟩, ?_⟩
    · exact single_mem_tDeg (b, a) z
    · have hv := eval_ne_zero_of_subset hI hs₀
      rw [locEmb_mk η M₀ hI m s (xyHom_map_C x η hse) hv, TwM.val_mk, single_mul_single]
      congr 1
      ext
      · simp
      · simp; omega
  · exact ⟨0, Submodule.zero_mem _, by rw [map_zero, single_zero]; rfl⟩
  · rintro u v _ _ ⟨w, hw, hwu⟩ ⟨w', hw', hwv⟩
    refine ⟨w + w', Submodule.add_mem _ hw hw', ?_⟩
    rw [map_add (f := _)]
    change UT.toL _ + UT.toL _ = _
    rw [hwu, hwv, single_add]
    rfl
  · rintro r' u _ ⟨w, hw, hwu⟩
    refine ⟨(C r' : MvPolynomial (Fin (r + 1)) S) • w, Submodule.smul_mem _ _ hw, ?_⟩
    rw [locEmb_smul', hwu, yHom_C, single_mul_single, zero_add, Algebra.smul_def]

end Loc

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZColumnsSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleZColumns.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (G : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h → ∀ I : Chart x,
      (∀ J J' : Chart h, J.1 ⊆ J'.1 →
        secsOnZChart G.toSubSystem H.toSubSystem h I J ≤ secsOnZChart G.toSubSystem H.toSubSystem h I J') ∧
      Cech.AugExact S (secsOnZChart G.toSubSystem H.toSubSystem h I) ((G.sub I).restrictScalars S)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZFamilySt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleZFamily.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h →
    ∃ F' : SubFamily S h E, ∀ J, (F'.sub J).restrictScalars S = secsOnZ F.toSubSystem H.toSubSystem h J

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZFiniteSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleZFinite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E), (∀ I, (F.sub I).FG) → ∀ (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h → ∀ J : Chart h, ∃ t : Finset E,
      (t : Set E) ⊆ secsOnZ F.toSubSystem H.toSubSystem h J ∧
      secsOnZ F.toSubSystem H.toSubSystem h J ≤ (Submodule.span (chartRing S h J) (t : Set E)).restrictScalars S

end

end GroundTheory.Heights₂.Heights.Kleiman
end

