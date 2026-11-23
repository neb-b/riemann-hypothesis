module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0572
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocommOfSurjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup.KerGrp


set_option autoImplicit false in
open CategoryTheory TensorProduct Coalgebra Bialgebra in
theorem _root_.GlobalTheory.PDivGroup.KerGrp.isCocomm_of_surjective {k A B : Type} [CommRing k] [CommRing A] [CommRing B]
    [Bialgebra k A] [Bialgebra k B] [IsCocomm k A] (f : A →ₐc[k] B)
    (hf : Function.Surjective f) : IsCocomm k B := by
  constructor
  ext b
  obtain ⟨a, rfl⟩ := hf b
  have hcomm : ∀ y : A ⊗[k] A, TensorProduct.comm k B B (TensorProduct.map (f : A →ₗ[k] B)
      (f : A →ₗ[k] B) y) = TensorProduct.map (f : A →ₗ[k] B) (f : A →ₗ[k] B)
      (TensorProduct.comm k A A y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hA : TensorProduct.comm k A A (comul a) = comul a :=
    LinearMap.congr_fun (Coalgebra.comm_comp_comul (R := k) (A := A)) a
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← CoalgHomClass.map_comp_comul_apply, hcomm, hA]


set_option autoImplicit false in
open CategoryTheory TensorProduct Coalgebra Bialgebra in
theorem _root_.GlobalTheory.PDivGroup.KerGrp.map_res_kerIdeal {p : ℕ} {k : Type} [CommRing k] {G H : _root_.GlobalTheory.PDivGroup p k} (u : G ⟶ H)
    (n : ℕ) : Ideal.map (G.res n : G.A (n + 1) →ₐ[k] G.A n) (_root_.GlobalTheory.PDiv.kerIdeal (u.app (n + 1))) =
      _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := by
  have hc := congrArg (fun g : H.A (n + 1) →ₐc[k] G.A n =>
    ((g : H.A (n + 1) →ₐ[k] G.A n) :
      H.A (n + 1) →+* G.A n))
    (_root_.GlobalTheory.PDivGroup.Hom.comm u n)
  have hres : Ideal.map (H.res n : H.A (n + 1) →ₐ[k]
      H.A n) (_root_.GlobalTheory.PDiv.augIdeal k (H.A (n + 1))) =
      _root_.GlobalTheory.PDiv.augIdeal k (H.A n) :=
    _root_.GlobalTheory.PDiv.kerIdeal_of_surjective (H.10 n)
  unfold _root_.GlobalTheory.PDiv.kerIdeal
  change Ideal.map ((G.res n : G.A (n + 1) →ₐ[k]
      G.A n) : G.A (n + 1) →+* G.A n)
      (Ideal.map ((u.app (n + 1) : H.A (n + 1) →ₐ[k]
        G.A (n + 1)) : H.A (n + 1) →+* G.A (n + 1))
        (_root_.GlobalTheory.PDiv.augIdeal k (H.A (n + 1)))) =
    Ideal.map ((u.app n : H.A n →ₐ[k] G.A n) :
      H.A n →+* G.A n)
      (_root_.GlobalTheory.PDiv.augIdeal k (H.A n))
  rw [Ideal.map_map]

  rw [show ((G.res n : G.A (n + 1) →ₐ[k] G.A n) :
      G.A (n + 1) →+* G.A n).comp
      ((u.app (n + 1) : H.A (n + 1) →ₐ[k] G.A (n + 1)) :
        H.A (n + 1) →+* G.A (n + 1)) =
      ((u.app n : H.A n →ₐ[k] G.A n) :
        H.A n →+* G.A n).comp
      ((H.res n : H.A (n + 1) →ₐ[k] H.A n) :
        H.A (n + 1) →+* H.A n) from hc, ← Ideal.map_map]
  rw [← hres]
  rfl

theorem exists_of_family {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k)
    (u : G ⟶ G) (h₀ : ℕ) (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, HopfAlgebra k (B n)]
    (π : ∀ n, G.A n →ₐc[k] B n) (hπ : ∀ n, Function.Surjective (π n))
    (hk : ∀ n, RingHom.ker (π n) = kerIdeal (u.app n))
    (h : ∀ n : ℕ, Module.finrank k (B n) = p ^ (n * h₀)) :
    ∃ (K : PDivGroup p k) (i : K ⟶ G), ∀ n : ℕ, Function.Surjective (i.app n) ∧
      RingHom.ker (i.app n) = kerIdeal (u.app n) := by
  haveI : ∀ n, IsCocomm k (B n) := fun n => isCocomm_of_surjective (π n) (hπ n)
  have hle : ∀ n, RingHom.ker (π (n + 1)) ≤ RingHom.ker ((π n).comp (G.res n)) := fun n a ha => by
    have : G.res n a ∈ RingHom.ker (π n) := by
      rw [hk, ← map_res_kerIdeal]
      rw [hk] at ha
      exact Ideal.mem_map_of_mem (G.res n : G.A (n + 1) →ₐ[k] G.A n) ha
    exact this
  let r := fun n => liftSurj (π (n + 1)) (hπ (n + 1)) ((π n).comp (G.res n)) (hle n)
  have hr : ∀ n a, r n (π (n + 1) a) = π n (G.res n a) := fun n a => liftSurj_apply ..
  let K : PDivGroup p k :=
    { height := h₀
      A := B
      finite := fun n => Module.Finite.of_surjective (π n : G.A n →ₗ[k] B n) (hπ n)
      rank_eq := fun n q => by rw [Module.rankAtStalk_eq_finrank_of_free, h]; rfl
      res := r
      res_surjective := fun n b => by
        obtain ⟨c, rfl⟩ := hπ n b
        obtain ⟨a, rfl⟩ := G.res_surjective n c
        exact ⟨_, hr n a⟩
      ker_res := fun n => by
        rw [← map_torsionIdeal (hπ (n + 1)), ← G.ker_res]
        refine le_antisymm (fun b hb => ?_) (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
        · obtain ⟨a, rfl⟩ := hπ _ b
          have h1 : G.res n a ∈ RingHom.ker (π n) := (hr n a).symm.trans hb
          rw [hk, ← map_res_kerIdeal] at h1
          obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective
            (G.res n : G.A (n + 1) →ₐ[k] G.A n) (G.res_surjective n)).1 h1
          rw [← hk] at hc
          have hc' : π (n + 1) c = 0 := hc
          have e' : G.res n c = G.res n a := e
          have h2 : a - c ∈ RingHom.ker (G.res n) := by
            rw [RingHom.mem_ker, map_sub, e', sub_self]
          have h3 : π (n + 1) a = π (n + 1) (a - c) := by rw [map_sub, hc', sub_zero]
          rw [h3]
          exact Ideal.mem_map_of_mem (π (n + 1) : G.A (n + 1) →ₐ[k] B (n + 1)) h2
        · have ha' : G.res n a = 0 := ha
          change r n (π (n + 1) a) = 0
          rw [hr, ha', map_zero] }
  exact ⟨K, ⟨π, fun n => BialgHom.ext fun a => hr n a⟩, fun n => ⟨hπ n, hk n⟩⟩


set_option autoImplicit false in
open CategoryTheory TensorProduct Coalgebra Bialgebra in
theorem _root_.GlobalTheory.PDivGroup.KerGrp.exists_kernel (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : _root_.GlobalTheory.PDivGroup p k)
    (u : G ⟶ G) (h₀ : ℕ)
    (h : ∀ n : ℕ, Module.finrank k (G.A n ⧸ _root_.GlobalTheory.PDiv.kerIdeal (u.app n)) = p ^ (n * h₀)) :
    ∃ (K : _root_.GlobalTheory.PDivGroup p k) (i : K ⟶ G), ∀ n : ℕ, Function.Surjective (i.app n) ∧
      RingHom.ker (i.app n) = _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := by
  classical
  obtain ⟨I, hIdef⟩ : ∃ I : ∀ n, Ideal (G.A n),
      ∀ n, I n = _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := ⟨_, fun n => rfl⟩
  haveI hH : ∀ n, (I n).IsHopfIdeal k := fun n => by
    rw [hIdef]
    exact _root_.GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom k _ _ (u.app n)
  have hq : ∀ n, Function.Surjective (Bialgebra.Quotient.mkBialgHom (R := k) (I n)) := by
    intro n x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, by simp⟩
  haveI hcoc : ∀ n, IsCocomm k (G.A n ⧸ I n) := fun n =>
    _root_.GlobalTheory.PDivGroup.KerGrp.isCocomm_of_surjective _ (hq n)
  have hmapI : ∀ n, Ideal.map (G.res n : G.A (n + 1) →ₐ[k]
      G.A n) (I (n + 1)) = I n := by
    intro n
    rw [hIdef, hIdef]
    exact _root_.GlobalTheory.PDivGroup.KerGrp.map_res_kerIdeal u n
  have hle : ∀ n, I (n + 1) ≤ (I n).comap (G.res n :
      G.A (n + 1) →ₐ[k] G.A n) := fun n =>
    Ideal.map_le_iff_le_comap.1 (hmapI n).le
  let φ : ∀ n, (G.A (n + 1) ⧸ I (n + 1)) →ₐ[k] (G.A n ⧸ I n) :=
    fun n => Ideal.quotientMapₐ (I n) (G.res n :
      G.A (n + 1) →ₐ[k] G.A n) (hle n)
  have hφ : ∀ n a, φ n (Ideal.Quotient.mk (I (n + 1)) a) =
      Ideal.Quotient.mk (I n) (G.res n a) := fun n a => rfl
  have hcounit : ∀ n, (Bialgebra.counitAlgHom k _).comp (φ n) =
      Bialgebra.counitAlgHom k (G.A (n + 1) ⧸ I (n + 1)) := by
    intro n
    refine AlgHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change CoalgebraStruct.counit (R := k) (Ideal.Quotient.mk (I n) (G.res n a)) =
      CoalgebraStruct.counit (R := k) (Ideal.Quotient.mk (I (n + 1)) a)
    rw [← Bialgebra.Quotient.mkBialgHom_apply (R := k), ← Bialgebra.Quotient.mkBialgHom_apply (R := k),
      CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply,
      CoalgHomClass.counit_comp_apply]
  have hcomul : ∀ n, (Algebra.TensorProduct.map (φ n) (φ n)).comp (Bialgebra.comulAlgHom k _) =
      (Bialgebra.comulAlgHom k _).comp (φ n) := by
    intro n
    refine AlgHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Algebra.TensorProduct.map (φ n) (φ n)
        (CoalgebraStruct.comul (R := k) (Ideal.Quotient.mk (I (n + 1)) a)) =
      CoalgebraStruct.comul (R := k) (Ideal.Quotient.mk (I n) (G.res n a))
    rw [← Bialgebra.Quotient.mkBialgHom_apply (R := k) (I (n + 1)),
      ← Bialgebra.Quotient.mkBialgHom_apply (R := k) (I n),
      ← CoalgHomClass.map_comp_comul_apply (Bialgebra.Quotient.mkBialgHom (R := k) (I (n + 1))),
      ← CoalgHomClass.map_comp_comul_apply (Bialgebra.Quotient.mkBialgHom (R := k) (I n)),
      ← CoalgHomClass.map_comp_comul_apply (G.res n)]
    generalize CoalgebraStruct.comul (R := k) a = y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hφ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  let r : ∀ n, (G.A (n + 1) ⧸ I (n + 1)) →ₐc[k] (G.A n ⧸ I n) :=
    fun n => BialgHom.ofAlgHom (φ n) (hcounit n) (hcomul n)
  have hr : ∀ n a, r n (Ideal.Quotient.mk (I (n + 1)) a) =
      Ideal.Quotient.mk (I n) (G.res n a) := fun n a => rfl
  have hrs : ∀ n, Function.Surjective (r n) := by
    intro n x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := G.10 n a
    exact ⟨Ideal.Quotient.mk _ b, hr n b⟩
  have hker : ∀ n, RingHom.ker (r n) =
      _root_.GlobalTheory.PDiv.torsionIdeal (R := k) (A := G.A (n + 1) ⧸ I (n + 1)) (p ^ n) := by
    intro n
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, hr, Ideal.Quotient.eq_zero_iff_mem,
      ← _root_.GlobalTheory.PDiv.map_torsionIdeal (hq (n + 1))]
    change _ ↔ Ideal.Quotient.mk (I (n + 1)) a ∈ Ideal.map (Ideal.Quotient.mk (I (n + 1))) _
    rw [Ideal.mem_quotient_iff_mem_sup, ← G.ker_res n]
    change a ∈ Ideal.comap (G.res n : G.A (n + 1) →ₐ[k]
      G.A n) (I n) ↔ _
    rw [← hmapI n, Ideal.comap_map_of_surjective (G.res n :
      G.A (n + 1) →ₐ[k] G.A n) (G.10 n),
      ← RingHom.ker_eq_comap_bot, sup_comm]
    all_goals rfl
  have hkq : ∀ n, RingHom.ker (Bialgebra.Quotient.mkBialgHom (R := k) (I n)) =
      _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := by
    intro n
    rw [← hIdef]
    ext x
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨_root_.GlobalTheory.PDivGroup.mk h₀ (fun n => G.A n ⧸ I n)
    (commRing := fun n => inferInstance) (hopf := fun n => inferInstance) (cocomm := hcoc)
    (finite := fun n => Module.Finite.of_surjective (Ideal.Quotient.mkₐ k (I n)).toLinearMap
      Ideal.Quotient.mk_surjective)
    (projective := fun n => inferInstance) (fun n q => ?_) r hrs hker,
    _root_.GlobalTheory.PDivGroup.Hom.mk (fun n => Bialgebra.Quotient.mkBialgHom (R := k) (I n))
      (fun n => ?_), fun n => ⟨hq n, ?_⟩⟩
  · rw [Module.rankAtStalk_eq_finrank_of_free]
    have hn := h n
    rw [← hIdef] at hn
    simpa using hn
  · exact DFunLike.ext _ _ fun a => rfl
  · exact hkq n

end GlobalTheory.PDivGroup.KerGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullSymplecticLevelStructureUniqueOfLevels
section
set_option autoImplicit false

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel

namespace GlobalTheory.FullLevel.Uniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem nsmul_cancel {n : ℕ} (hn : n ≠ 0) {x y : D.La} (h : n • x = n • y) : x = y := by
  apply D.unimod.1
  ext w
  have h1 := congrArg (fun t => D.EF t w) h
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h1
  exact mul_left_cancel₀ (by exact_mod_cast hn) h1

theorem mem_of_dvd {M : ℕ} (hM : M ≠ 0) {x : D.La} (h : ∀ y, (M : ℤ) ∣ D.EF x y) : ∃ u, x = M • u := by
  have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM
  choose f hf using h
  let φ : D.La →ₗ[ℤ] ℤ :=
    { toFun := f
      map_add' := fun a b => by
        apply mul_left_cancel₀ hM'
        rw [mul_add, ← hf, ← hf, ← hf, map_add (f := _)]
      map_smul' := fun c a => by
        apply mul_left_cancel₀ hM'
        rw [← hf, map_smul, hf]
        simp only [smul_eq_mul, RingHom.id_apply]
        ring }
  obtain ⟨u, hu⟩ := D.unimod.2 φ
  refine ⟨u, D.unimod.1 ?_⟩
  ext w
  rw [map_nsmul, LinearMap.smul_apply, hu, hf, nsmul_eq_mul]
  rfl

theorem mem_lcm {M A : ℕ} (hM : M ≠ 0) {x u v : D.La} (hu : x = M • u) (hv : x = A • v) :
    ∃ w, x = Nat.lcm M A • w := by
  have hg : Nat.gcd M A ≠ 0 := fun h => hM (Nat.eq_zero_of_gcd_eq_zero_left h)
  refine ⟨Nat.gcdA M A • v + Nat.gcdB M A • u, nsmul_cancel hg ?_⟩
  rw [← mul_nsmul', Nat.gcd_mul_lcm, ← natCast_zsmul x, Nat.gcd_eq_gcd_ab, add_zsmul, smul_add]
  congr 1
  · rw [hv, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  · rw [hu, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
  {N : ℕ} {z : kˣ} {ev : D.La → Q}

theorem ev_zero (h : IsSympLevel D act e N z ev) : ev 0 = 1 := (h.2.2.1 0).2 ⟨0, by simp⟩

theorem ev_nsmul (h : IsSympLevel D act e N z ev) (n : ℕ) (a : D.La) : ev (n • a) = ev a ^ n := by
  induction n with
  | zero => simp [ev_zero h]
  | succ n ih => rw [succ_nsmul, h.1, ih, pow_succ]

theorem ev_eq_iff (h : IsSympLevel D act e N z ev) (x y : D.La) : ev x = ev y ↔ ∃ b, x - y = N • b := by
  rw [← h.2.2.1]
  have h1 : ev x = ev (x - y) * ev y := by rw [← h.1, sub_add_cancel]
  rw [h1]
  exact mul_eq_right

theorem ev_pow_eq (h : IsSympLevel D act e N z ev) (hN : 0 < N) {A : ℕ} (hA : A ∣ N) {x y : D.La}
    (hxy : ev x ^ (N / A) = ev y ^ (N / A)) : ∃ b, x - y = A • b := by
  obtain ⟨m, hm⟩ := hA
  have hA0 : 0 < A := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm; omega
  have hd : N / A = m := by rw [hm, Nat.mul_div_cancel_left _ hA0]
  rw [hd, ← ev_nsmul h, ← ev_nsmul h, ev_eq_iff h] at hxy
  obtain ⟨b, hb⟩ := hxy
  refine ⟨b, nsmul_cancel hm0 ?_⟩
  rw [smul_sub, hb, hm, smul_smul, mul_comm]

end GlobalTheory.FullLevel.Uniq

namespace GlobalTheory.FullLevel

open Uniq

theorem isSympLevel_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H)
    {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (he : ∀ (g g' : Q) (c c' : kˣ), e l.M' g g' c → e l.M' g g' c' → c = c')
    {z : kˣ} (hz : IsPrimitiveRoot z l.M') {etaA eta ev ev' : D.La → Q}
    (h : IsSympLevel D act e l.M' z ev) (hi : Induces l etaA eta ev)
    (h' : IsSympLevel D act e l.M' z ev') (hi' : Induces l etaA eta ev') : ev = ev' := by
  have hM' := M'_pos l
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hex : ∀ a, ∃ x, ev x = ev' a := fun a =>
    (h.2.2.2.1 _).1 ((h'.2.2.2.1 _).2 ⟨a, rfl⟩)
  choose g hg using hex
  have h1 : ∀ a, ∃ b, g a - a = l.A • b := fun a =>
    ev_pow_eq h hM' (A_dvd_M' l) (by rw [hg, hi'.1, hi.1])
  have h2 : ∀ c ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), ∀ a : D.La, ∃ b, g (c • a) - c • a = l.M • b := by
    intro c hc a
    have hmem : c • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
      Submodule.smul_mem_smul hc Submodule.mem_top
    exact ev_pow_eq h hM' (M_dvd_M' l) (by rw [hg, hi'.2 _ hmem, hi.2 _ hmem])
  have h3 : ∀ a b, (l.M : ℤ) ∣ D.EF (g a) (g b) - D.EF a b := by
    intro a b
    have e1 := h.2.2.2.2 (g a) (g b)
    rw [hg, hg] at e1
    have e2 := he _ _ _ _ e1 (h'.2.2.2.2 a b)
    have e3 : z ^ (D.EF (g a) (g b) - D.EF a b) = 1 := by rw [zpow_sub, e2, mul_inv_cancel]
    exact (Int.natCast_dvd_natCast.2 (M_dvd_M' l)).trans ((hz.zpow_eq_one_iff_dvd _).1 e3)
  obtain ⟨n, hn, m, hm, hnm⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ _ from l.coprime ▸ Submodule.mem_top)
  funext a
  have h4 : ∃ u, m • (g a - a) = l.M • u := by
    obtain ⟨b, hb⟩ := h2 m hm a
    obtain ⟨c, hc⟩ := (ev_eq_iff h (m • g a) (g (m • a))).1 (by rw [h.2.1, hg, hg, h'.2.1])
    obtain ⟨t, ht⟩ := M_dvd_M' l
    refine ⟨t • c + b, ?_⟩
    rw [smul_add, smul_smul, ← ht, ← hc, ← hb, smul_sub]
    abel
  have h5 : ∃ u, n • (g a - a) = l.M • u := by
    refine mem_of_dvd hM fun y => ?_
    obtain ⟨b, hb⟩ := h2 (H.bar n) (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hn) y
    have h6 := h3 a (H.bar n • y)
    rw [sub_eq_iff_eq_add] at hb
    rw [hb, map_add (f := _), map_nsmul, nsmul_eq_mul, add_sub_assoc, dvd_add_right (dvd_mul_right _ _)] at h6
    rw [D.adj, map_sub, LinearMap.sub_apply]
    exact h6
  obtain ⟨u, hu⟩ := h4
  obtain ⟨v, hv⟩ := h5
  obtain ⟨b, hb⟩ := h1 a
  have h7 : g a - a = l.M • (v + u) := by rw [smul_add, ← hu, ← hv, ← add_smul, hnm, one_smul]
  rw [← hg]
  exact ((ev_eq_iff h _ _).2 (mem_lcm hM h7 hb)).symm

end GlobalTheory.FullLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGaloisCoverGrpSchemeSquareProductMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke.ProdGalois
variable {S : Scheme.{0}}

theorem transl_lift_fst {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A) ≫ fst A A = fst A A ≫ transl h₁ := by
  rw [transl, transl, mul_comp, comp_mul, Category.id_comp, Category.comp_id, Category.assoc, lift_fst,
    ← Category.assoc, toUnit_unique (fst A A ≫ toUnit A) (toUnit _)]

theorem transl_lift_snd {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A) ≫ snd A A = snd A A ≫ transl h₂ := by
  rw [transl, transl, mul_comp, comp_mul, Category.id_comp, Category.comp_id, Category.assoc, lift_snd,
    ← Category.assoc, toUnit_unique (snd A A ≫ toUnit A) (toUnit _)]

theorem transl_lift_fst_left {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    (transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A)).left ≫ (fst A A).left = (fst A A).left ≫ (transl h₁).left := by
  rw [← Over.comp_left, transl_lift_fst, Over.comp_left]

theorem transl_lift_snd_left {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    (transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A)).left ≫ (snd A A).left = (snd A A).left ≫ (transl h₂).left := by
  rw [← Over.comp_left, transl_lift_snd, Over.comp_left]

theorem grpScheme_square_hom_ext_fst_snd {A : Over S} {X : Scheme.{0}} {a b : X ⟶ (G2 A).left}
    (h₁ : a ≫ (fst A A).left = b ≫ (fst A A).left) (h₂ : a ≫ (snd A A).left = b ≫ (snd A A).left) : a = b :=
  pullback.hom_ext h₁ h₂

theorem grpSchemeSquareProductMap_comp_fst {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ ≫ (fst A' A').left = (fst A A).left ≫ ψ.left := by
  rw [sq2, ← Over.comp_left, lift_fst, Over.comp_left]

theorem grpSchemeSquareProductMap_comp_snd {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ ≫ (snd A' A').left = (snd A A).left ≫ ψ.left := by
  rw [sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem grpSchemeSquareProductMap_eq_pullback_map {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ = pullback.map A.hom A.hom A'.hom A'.hom ψ.left ψ.left (𝟙 S) (by simp) (by simp) := by
  apply grpScheme_square_hom_ext_fst_snd
  · rw [grpSchemeSquareProductMap_comp_fst]; exact (pullback.lift_fst _ _ _).symm
  · rw [grpSchemeSquareProductMap_comp_snd]; exact (pullback.lift_snd _ _ _).symm

end GlobalTheory.UPel.HT.Hecke.ProdGalois


open GlobalTheory.UPel.HT.Hecke.ProdGalois in
theorem GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → GlobalTheory.ZM.IsGaloisCover (G × G) (fun h => (GlobalTheory.UPel.HT.Hecke.transl (lift h.1.1 h.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left) (GlobalTheory.UPel.HT.Hecke.sq2 ψ) := by
  intro S A A' _ _ _ _ G ψ _ hψ
  have := hψ.finite
  have hfin := hψ.fin
  have het := hψ.etale
  have hon := hψ.onto
  refine
    { finite := inferInstance
      one := ?_
      mul := ?_
      inv := ?_
      fin := ?_
      etale := ?_
      onto := ?_
      fibre := ?_ }
  · apply grpScheme_square_hom_ext_fst_snd
    · rw [transl_lift_fst_left, Category.id_comp]
      have e := hψ.one
      rw [show ((1 : G × G).1 : 𝟙_ (Over S) ⟶ A) = ((1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e, Category.comp_id]
    · rw [transl_lift_snd_left, Category.id_comp]
      have e := hψ.one
      rw [show ((1 : G × G).2 : 𝟙_ (Over S) ⟶ A) = ((1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e, Category.comp_id]
  · intro a c
    apply grpScheme_square_hom_ext_fst_snd
    · rw [transl_lift_fst_left, Category.assoc, transl_lift_fst_left, reassoc_of% transl_lift_fst_left]
      have e := hψ.mul a.1 c.1
      rw [show ((a * c).1 : 𝟙_ (Over S) ⟶ A) = ((a.1 * c.1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e]
    · rw [transl_lift_snd_left, Category.assoc, transl_lift_snd_left, reassoc_of% transl_lift_snd_left]
      have e := hψ.mul a.2 c.2
      rw [show ((a * c).2 : 𝟙_ (Over S) ⟶ A) = ((a.2 * c.2 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e]
  · intro a
    apply grpScheme_square_hom_ext_fst_snd
    · rw [Category.assoc, grpSchemeSquareProductMap_comp_fst, reassoc_of% transl_lift_fst_left, hψ.inv a.1]
    · rw [Category.assoc, grpSchemeSquareProductMap_comp_snd, reassoc_of% transl_lift_snd_left, hψ.inv a.2]
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    exact MorphismProperty.pullbackMap (P := @IsFinite) hfin hfin (Over.w ψ).symm (Over.w ψ).symm
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    haveI : MorphismProperty.IsStableUnderComposition @Etale.{0} := ⟨fun _ _ _ _ ↦ inferInstance⟩
    exact MorphismProperty.pullbackMap (P := @Etale) het het (Over.w ψ).symm (Over.w ψ).symm
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    haveI : MorphismProperty.IsStableUnderComposition @Surjective.{0} := ⟨fun _ _ _ _ ↦ inferInstance⟩
    exact MorphismProperty.pullbackMap (P := @Surjective) hon hon (Over.w ψ).symm (Over.w ψ).symm
  · intro K _ _ y y' e
    have e₁ : (y ≫ (fst A A).left) ≫ ψ.left = (y' ≫ (fst A A).left) ≫ ψ.left := by
      rw [Category.assoc, Category.assoc, ← grpSchemeSquareProductMap_comp_fst, reassoc_of% e]
    have e₂ : (y ≫ (snd A A).left) ≫ ψ.left = (y' ≫ (snd A A).left) ≫ ψ.left := by
      rw [Category.assoc, Category.assoc, ← grpSchemeSquareProductMap_comp_snd, reassoc_of% e]
    obtain ⟨a₁, ha₁, hu₁⟩ := hψ.fibre K _ _ e₁
    obtain ⟨a₂, ha₂, hu₂⟩ := hψ.fibre K _ _ e₂
    refine ⟨(a₁, a₂), ?_, ?_⟩
    · apply grpScheme_square_hom_ext_fst_snd
      · rw [Category.assoc, transl_lift_fst_left, ← Category.assoc]; exact ha₁
      · rw [Category.assoc, transl_lift_snd_left, ← Category.assoc]; exact ha₂
    · intro b hb
      refine Prod.ext (hu₁ b.1 ?_) (hu₂ b.2 ?_)
      · show (y ≫ (fst A A).left) ≫ (transl (b.1 : 𝟙_ (Over S) ⟶ A)).left = y' ≫ (fst A A).left
        rw [Category.assoc, ← transl_lift_fst_left _ (b.2 : 𝟙_ (Over S) ⟶ A), ← Category.assoc]
        exact congrArg (· ≫ (fst A A).left) hb
      · show (y ≫ (snd A A).left) ≫ (transl (b.2 : 𝟙_ (Over S) ⟶ A)).left = y' ≫ (snd A A).left
        rw [Category.assoc, ← transl_lift_snd_left (b.1 : 𝟙_ (Over S) ⟶ A), ← Category.assoc]
        exact congrArg (· ≫ (snd A A).left) hb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCupProduct_graded_comm : ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring) := by
  first
  | exact @GlobalTheory.EtC.cup_comm
  | exact GlobalTheory.EtC.cup_comm
  | (intros; apply GlobalTheory.EtC.cup_comm <;> assumption)
end

